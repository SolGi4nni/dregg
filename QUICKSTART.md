# dregg in 15 minutes

This is the hands-on path: talk to the live devnet, sign a real turn, run the
guided demo, run the site (playground / explorer / starbridge) locally, and
drive a governance ceremony on the real executor. Every command below was run
successfully against this tree; outputs are pasted (truncated) as the expected
result.

What you need: this repo, `cargo`, `curl`. Docker only for the site section.

---

## 1. Talk to the live devnet (60 seconds, no build)

A public node runs at `https://devnet.dregg.fg-goose.online` (solo-federation
devnet, verified-Lean state producer, faucet on).

```sh
curl -s https://devnet.dregg.fg-goose.online/status
```

```json
{"healthy":true,"peer_count":0,"dag_height":2798,"consensus_live":true,
 "federation_mode":"solo","state_producer":"lean","lean_producer":true,
 "full_turn_proving":true,"producer_covered_effects":19}
```

Faucet yourself a cell — any fresh 32-byte id works as a recipient
(`python3 -c "import secrets;print(secrets.token_hex(32))"` makes one):

```sh
curl -s -X POST https://devnet.dregg.fg-goose.online/api/faucet \
  -H 'content-type: application/json' \
  -d '{"recipient":"28c2cba0ccfd29e8c2cb2773f398dfb652a94fa49dbcb143643cd4df847a076f","amount":1000}'
```

```json
{"success":true,"tx_hash":"5ddf8f19a6d3bbbb8a11c9120f27c1debb6be64e899a4ff83a2ff806abdae63b","amount":1000}
```

Read your cell back (and see it in the explorer at
`https://devnet.dregg.fg-goose.online/explorer/cell/<your-cell-id>`):

```sh
curl -s https://devnet.dregg.fg-goose.online/api/cell/28c2cba0ccfd29e8c2cb2773f398dfb652a94fa49dbcb143643cd4df847a076f
```

```json
{"id":"28c2cba0…","found":true,"balance":1000,"nonce":0,…}
```

## 2. Get the CLI

```sh
cargo build -p dregg-cli --release
export PATH="$PWD/target/release:$PATH"        # or invoke ./target/release/dregg
export DREGG_NODE_URL=https://devnet.dregg.fg-goose.online
dregg node status
```

```text
=== Node Status ===
  Health: HEALTHY
  Federation mode: solo
  State producer: LEAN (verified, 19 effects)
  Full-turn proving: on (STARK per turn)
  DAG height: 2,798
```

`dregg doctor` health-checks the whole client surface; `dregg --help` lists
the verbs (id, cell, turn, name, polis, voting, bounty, cap, proof, …).

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
+---------+-----------------------+
| Name    | Public key            |
+=================================+
| * ember | 72cf3c9bcc58...466e6b |
+---------+-----------------------+
  Active: ember (persistent default)
```

`DREGG_PROFILE=<name>` overrides the persistent default per-shell.

## 3. Sign a real turn

Reads are public; **writes need the node's bearer token** (the node signs
turns with its operator cipherclerk). Two ways to have one:

- **Your own node** (next section): `POST /cipherclerk/unlock` returns
  `bearer_token`, or just use `dregg demo --passphrase`, which does it for you.
- **The shared devnet**: the token lives on the instance as
  `DEVNET_API_TOKEN` in `/etc/dregg/node.env`. If you operate the box:

  ```sh
  export DREGG_API_TOKEN=$(ssh -i ~/.ssh/negneg-cq.pem ubuntu@34.224.208.52 \
      'sudo grep ^DEVNET_API_TOKEN /etc/dregg/node.env | cut -d= -f2')
  ```

Submit one effect — write a field of the operator's own cell (`agent` is
advisory; the node derives the real signer from its cipherclerk):

```sh
curl -s -X POST https://devnet.dregg.fg-goose.online/api/turns/submit \
  -H "Authorization: Bearer $DREGG_API_TOKEN" -H 'content-type: application/json' \
  -d '{"agent":"'"$(curl -s $DREGG_NODE_URL/api/node/identity | python3 -c 'import json,sys;print(json.load(sys.stdin)["agent_cell"])')"'",
       "nonce":0,"fee":1000,"memo":"hello from the quickstart",
       "actions":[{"effects":[{"kind":"set_field","index":0,"value":"42"}]}]}'
```

```json
{"accepted":true,"turn_hash":"8dae2ff19fb5e2912fb4dc76b1d0693cdc702a5b2194b0540ccbd79b2eccfff8",
 "proof_status":"proof_pending","has_witness":false,"witness_count":0,"error":null}
```

Watch the receipt land:

```sh
curl -s https://devnet.dregg.fg-goose.online/api/receipts          # the chain, newest first
dregg turn status 8dae2ff19fb5e2912fb4dc76b1d0693cdc702a5b2194b0540ccbd79b2eccfff8
```

```text
=== Turn Receipt ===
  Turn hash: 8dae2ff1...fff8
  Finality: tentative
  Chain index: 8
  Actions: 1
  Computrons: 422
  Pre-state: 6bc3a65e...6a29
  Post-state: abd79a4a...5a0b
  Proof: none
  Witnessed: yes
  Witness count: 1
```

(One honest caveat: on the shared devnet the per-turn STARK currently stays
`proof_pending` — the witness lands immediately, the proof attachment is a
known gap; see "rough edges" at the bottom. On a local node with
`--prove-turns` off you simply get `Full-turn proving: off`.)

## 4. The guided demo — a full app lifecycle, one command

`dregg demo` drives the whole nameservice machine — faucet → register →
resolve → transfer → revoke — each step a real signed turn:

```sh
dregg demo --name you.dregg            # uses DREGG_API_TOKEN against the devnet
```

```text
=== Step 2: Unlocking the cipherclerk ===
OK: Node already unlocked; using your configured bearer token.
=== Step 3: Funding the operator cell ===
OK: Funded 5000 computrons.
=== Step 4: Registering 'you.dregg' ===
OK: Registration committed     Turn: f3ce5e21...8a93
=== Step 5: Resolving 'you.dregg' ===
OK: 'you.dregg' is bound and active
=== Step 6: Transferring 'you.dregg' to bob ===
OK: Transfer committed
=== Step 7: Revoking 'you.dregg' (one-way) ===
OK: Revocation committed
ERROR: REVOKED — this name has been tombstoned (one-way).   ← the point!
=== Demo complete ===
```

### …or against your own node (no token dance, full unlock flow)

```sh
cargo build -p dregg-node                 # once; the verified Lean producer is default-on
./target/debug/dregg-node init --data-dir /tmp/my-dregg
./target/debug/dregg-node run  --data-dir /tmp/my-dregg --enable-faucet --port 8421 &
dregg --node-url http://localhost:8421 demo --passphrase pick-a-passphrase
```

Same lifecycle; the first unlock SETS the passphrase on a fresh node, and the
demo acquires the bearer token itself.

## 5. Run the site locally (playground · explorer · starbridge)

The site builds in Docker (`node:22`); mount the **repo root** — the build
regenerates its ontology/predicate catalogs from the Lean sources in
`metatheory/`:

```sh
docker run --rm -v "$PWD:/repo" -w /repo/site node:22 \
  sh -c "npm install --no-audit --no-fund && npm run build"
docker run --rm -d -p 3000:3000 -v "$PWD/site:/site" -w /site node:22 npx serve dist
```

(If the build aborts with "generated catalogs are stale", run it as
`sh -c "node tools/gen-ontology-catalog.js && npm run build"` — the Lean
sources moved under it.)

Then:

- **<http://localhost:3000/playground/#turn-workbench>** — stage a turn by
  verb, read the verified-Lean explanation, RUN it on the real in-browser wasm
  executor, then PROVE it: a real EffectVM STARK, produced and self-verified
  in your browser (~500 KB proof, 64 trace rows for one SetField).
- **<http://localhost:3000/explorer/>** — defaults to `http://localhost:8420`;
  open Settings and point it at `https://devnet.dregg.fg-goose.online` (or your
  `:8421` node) to browse live cells/receipts with witness status and per-cell
  time travel. The hosted twin (same build) is
  <https://devnet.dregg.fg-goose.online/explorer/>.
- **<http://localhost:3000/starbridge/>** — the workbench/inspector. It boots
  an EMPTY in-browser world: use the **Start here** strip (seed a sandbox
  world → run a transfer turn → click the receipt), or switch the Runtime
  picker to *remote* to browse the devnet read-only.

## 6. Drive a governance ceremony (polis)

The polis council machine — charter, proposal, M-of-N approvals, threshold
certification, execute-exactly-once — runs end-to-end on the real executor in
one example binary:

```sh
cargo run -p dregg-sdk --example polis_ceremony
```

```text
charter             : 2-of-3
proposal cell born  : 6628d2df8c0321b8…
[propose] state=Proposed approvals=0/2 certified=false
[approve] state=Proposed approvals=1/2 certified=false
certify at 1-of-2   : EXECUTOR REJECTED (as it must) — program violation on cell …: affine sum 1 > 0
[certify] state=Approved approvals=2/2 certified=true
[execute] state=Executed approvals=2/2 certified=true
grantee balance     : 100 (treasury paid exactly once)
```

Every rule there is enforced by the cell program the factory installs — the
SDK builds turns, the EXECUTOR rejects the bad ones. The same machine on a
live node decodes with `dregg polis council --cell <proposal-cell-id>`.
(`sdk/tests/polis_governance_e2e.rs` is the full tooth-by-tooth suite,
including the constitution + forward-certified amendment ceremony.)

Also try `cargo run -p dregg-sdk --example hello_receipt_chain` — the smallest
possible "what is a receipt" loop.

## 7. Inspect what you made

```sh
dregg cell inspect <cell-id>                  # state, nonce, program, c-list
dregg name resolve you.dregg --cell <cell>    # the name machine, decoded
dregg polis council --cell <proposal-cell>    # the council machine, decoded
dregg turn status <turn-hash>                 # receipt, finality, witness
```

and in a browser: `https://devnet.dregg.fg-goose.online/explorer/cell/<id>`
(also `…/explorer/receipt/<hash>`, `…/explorer/tx/<turn-hash>`).

## Where next

- `starbridge-apps/` — the app layer (nameservice, polis, privacy-voting,
  bounty-board, identity, …); each crate's `lib.rs` documents its machine and
  what the substrate enforces. `dregg voting` / `dregg bounty` drive the
  voting/bounty machines on a node whose genesis seeds those cells.
- `sdk/` — `AgentRuntime` (embedded executor), factories, polis builders;
  `sdk/tests/*_e2e.rs` are executable specifications.
- `metatheory/` — the verified Lean implementation the node runs.
- The paper: <https://devnet.dregg.fg-goose.online/paper.html>.

## Known rough edges (devnet, 2026-06)

- The shared devnet's reverse proxy forwards only an allowlist of paths; the
  CLI therefore uses the `/api/turns/*` aliases. Endpoints without aliases
  (`/cipherclerk/unlock`, `/turn/atomic`, `/turns/peer-exchange`,
  `/cells/create-from-factory`) are local-node-only for now.
- Per-turn STARK attachment on the shared devnet stays `proof_pending`
  (witnesses land; the async prove pool isn't attaching proofs).
- Thin-HTTP turns currently marshal without `valid_until`, so the Lean
  producer logs a fallback-to-Rust for them (`turn.valid_until required for
  wire marshal`) — execution is unaffected, but those turns don't ride the
  verified producer yet.
- The devnet's data dir predates starbridge genesis seeding, so the seeded
  app cells (`privacy-voting-poll`, `bounty-board-bounty`, …) don't exist
  there; `dregg voting`/`dregg bounty` need a freshly-initialized node.
