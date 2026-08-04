# Path of Angels devnet operator kit

`scripts/poa-devnet.sh` creates and runs a federation that is cryptographically
and operationally separate from the main Dregg federation.  It is a wrapper
around the real `dregg-node` APIs, not another implementation of genesis,
joining, or membership:

- `dregg-node genesis --deployment-domain
  pathofangels.network/federation/v1 --no-demo-economy` makes the hybrid
  committee and descriptor;
- `dregg-node gen-validator-key` derives/checks every public identity;
- `dregg-node join` pins that descriptor, catches up as a non-voting follower,
  and auto-proposes the follower on-chain;
- `propose-epoch-transition` and `approve-membership` are the live membership
  verbs;
- `status`, `/status`, and `/api/membership` are the liveness and chain-identity
  probes.

The checked deployment manifest is `<POA_ROOT>/poa-devnet.json`.  It binds the
protocol domain, committee-derived federation id, exact genesis bytes, separate
node roots, public keys, ports, and advertised gossip topology.  Operator env
files are consumed by the launcher and translated into explicit `dregg-node
run` flags.  Verification requires each file to be byte-for-byte derivable from
the manifest before a safe, non-evaluating parser reads it, so an edited env file
cannot redirect a node to main storage, different ports, or different peers.

## Isolation guarantees

Generation and every later `verify` refuse:

- a PoA root equal to, containing, or contained by the main data root;
- the main federation id;
- a validator, issuer, fee-well, or follower key reused from main;
- an issuer/fee public identity appearing in both genesis descriptors;
- duplicate validator or follower keys, or a serving key that is not an exact
  copy of its one authoritative bundle seed;
- a changed or differently copied `genesis.json`;
- overlapping HTTP/gossip ports;
- the `.devnet` marker in any serving directory (it silently enables automatic
  Join approval);
- a faucet key, a genesis value move, a non-zero generic balance, or the generic
  Starbridge demo catalog.

The PoA profile consequently starts with two zero-balance, deployment-scoped
wells and no generic `$DREGG`/computron issuance.  The launcher never passes
`--enable-faucet`, `--auto-approve-joins`, or
`DREGG_ALLOW_UNVERIFIED_CONSENSUS`.  Every local, printed-remote, and follower
command explicitly sets `DREGG_REQUIRE_LEAN=1`,
`DREGG_STRAND_ADMISSION_GATE=1`, and
`DREGG_ALLOW_UNVERIFIED_CONSENSUS=0`; inherited opt-outs are refused. It always
passes `--prove-turns` and checks
that `/status` reports both the Lean producer and full-turn proving.  Aggregate
private-activity counts stay off the public status surface.

## Make the federation

Use a Lean-linked node binary.  A local three-process mesh is the default:

```sh
export POA_BIN="$PWD/target/release/dregg-node"
export POA_ROOT="$HOME/.local/share/path-of-angels/devnet"
export POA_MAIN_DATA_DIR="$HOME/.dregg"

scripts/poa-devnet.sh genesis
scripts/poa-devnet.sh up
scripts/poa-devnet.sh health
```

Ports start at HTTP `8421` and gossip `9421`.  `up` is deliberately a
one-host launcher and refuses a multi-host manifest.

For hbox, persvati, and a temporary third operator, advertise addresses when
generating (Headscale DNS names or overlay IPv4 addresses, without ports):

```sh
export POA_NODE_HOSTS='hbox.poa,persvati.poa,cipherclerk.poa'
scripts/poa-devnet.sh genesis
```

Distribute `poa-devnet.json`, the public `bundle/genesis.json`, the chosen
`nodes/node-N/` directory, this launcher, and the binary over the private
overlay, under the same `POA_ROOT` path on each host.  Do **not** copy any
`bundle/node-N.key`: the rest of `bundle/` is the provisioning archive and
contains all three validator seeds. Each operator receives exactly one
`node.key`. On each destination host, print its command with that host's API
bind address only after the public manifest and local operator package verify:

```sh
# hbox
scripts/poa-devnet.sh operator-command 0 100.70.0.10

# persvati
scripts/poa-devnet.sh operator-command 1 100.70.0.11

# temporary Cipherclerk host
scripts/poa-devnet.sh operator-command 2 100.70.0.12
```

Each command retains its own `node.key` and data path while peering to the
other two advertised hosts.  Do not use `0.0.0.0`; bind the overlay address and
put the public HTTP edge behind the existing authenticated reverse proxy.

Three validators have threshold three under Dregg's strict supermajority rule,
so the initial mesh tolerates no offline validator.  Four is the first size
that tolerates one fault; change `POA_VALIDATORS` and provide the same number of
advertised hosts if operational slack matters more than the three-host beta
shape.

## Follower-first participation

Anyone can make a fresh identity, pin the public descriptor, and verify the
lace before receiving voting authority.  The public follower package is only
`poa-devnet.json` plus `bundle/genesis.json`; it contains no validator seed:

```sh
scripts/poa-devnet.sh follower-init deck-447
scripts/poa-devnet.sh follower-command deck-447 hbox.poa:9421 100.70.0.44
# Run the printed command. `join` catches up, follows, and auto-proposes.
```

The candidate can inspect `/api/membership`.  A current operator can open the
same proposal explicitly and later approve its exact proposal block:

```sh
scripts/poa-devnet.sh propose deck-447 0
scripts/poa-devnet.sh approve <proposal-block-hex> 0
```

Proposing is not admission.  Only finalized current-committee votes change the
live committee.

## Admission readiness is intentionally red

The protocol target in `docs/reference/PATH-OF-ANGELS-PROTOCOL.md` is the Lean
F-4 two-vouch, finite least-fixed-point policy.  At the time this kit landed,
the production node still feeds the admission gate `candidates == participants`
and supplies no live vouch/bond rows.  Therefore this kit honestly records:

```text
admission = committee-ratified-manual-v1
f4_transitive_vouch_rows_live = false
objective_vouch_admission_ready = false
```

`scripts/poa-devnet.sh readiness` is a hard release gate: it performs the
normal health probes and then exits red until the live node actually derives
candidate/vouch rows from chain state.  Do not describe this initial committee
approval path as F-4, objective, or trustless admission merely because the
Lean theorem exists.

## Verification

The deployment-policy tests are fast and do not synthesize PQ keys:

```sh
node --test scripts/tests/poa-devnet-manifest.test.mjs
bash -n scripts/poa-devnet.sh
node --check scripts/poa-devnet-manifest.mjs
```

The node-side domain-key tests are narrow:

```sh
cargo nextest run -p dregg-node -E 'test(/deployment_domain/)'
```

For a live mesh, `health` additionally requires the manifest federation id at
`/api/membership`, full consensus mode, the Lean producer, full-turn proving,
and absence of public private-volume counters.
