# Path of Angels devnet operator kit

`scripts/poa-devnet.sh` creates and runs a federation that is cryptographically
and operationally separate from the main Dregg federation.  It is a wrapper
around the real `dregg-node` APIs, not another implementation of genesis,
joining, or membership:

- `dregg-node genesis --deployment-domain
  pathofangels.network/federation/v1 --no-demo-economy` makes the hybrid
  committee and descriptor;
- `dregg-node gen-validator-key` derives/checks every public identity;
- `dregg-node join --follow-only` pins that descriptor and catches up as a
  proposal-neutral, non-voting observer; ordinary `join` retains its historical
  auto-propose behavior for an operator who deliberately applies to join;
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

The public, key-free epoch-1 follower package is checked in at
`poa/deployments/epoch-1/`. It contains only:

- the exact live `poa-devnet.json` and byte-identical `bundle/genesis.json`;
- the active release receipt;
- `release-lock.json`, which cross-pins the federation, deployment, genesis,
  Lean-linked node binary, semantic source tree, source commit, portable OCI
  image identity, runtime base, Linux gate receipt, bootstrap peers, and
  receipted runtime capabilities;
- the exact portable-image identity verifier named by the receipt.

It contains no `.key`, operator env, ledger, invitation password, or curator
material. `scripts/poa-follower-package.mjs` refuses an unexpected path, a
changed locked byte, or any release/deployment disagreement.

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
- a faucet key, the generic Starbridge demo catalog, or any genesis value beside
  the single named player grant described below.

The PoA profile consequently starts with two deployment-scoped wells and no
generic `$DREGG`/computron issuance.  The launcher never passes
`--enable-faucet`, `--auto-approve-joins`, or
`DREGG_ALLOW_UNVERIFIED_CONSENSUS`.  Every local, printed-remote, and follower
command explicitly sets `DREGG_REQUIRE_LEAN=1`,
`DREGG_STRAND_ADMISSION_GATE=1`, and
`DREGG_ALLOW_UNVERIFIED_CONSENSUS=0`; inherited opt-outs are refused. It always
passes `--prove-turns` and checks
that `/status` reports both the Lean producer and full-turn proving.  Aggregate
private-activity counts stay off the public status surface.

## The player grant — the only value on the chain

⚑ **A PoA turn is not free, and a PoA chain has no faucet.** A Signal claim costs
`dregg_sdk::poa_signal::signal_claim_fee_v1()` — **870** computrons at
`ComputronCosts::default()`. The executor refuses any agent whose balance is under
the fee (`insufficient balance on cell …: need 870, have N`); `POST /api/faucet` is
off by policy *and* has no genesis faucet cell to spend from; and `Effect::Mint`
needs a fee the zero-balance issuer well cannot pay either.

Until 2026-08-07 a PoA genesis therefore held **no value at all** — two
zero-balance wells and no moves — so no player could pay for a turn and
`latest_height` was pinned to 0 by the descriptor. The federation verified, booted
and reported `healthy: true` the whole time.

`POA_PLAYER_GRANT` (default `1000000`) fixes it with **one issuer-move** into a
deployment-local **player-grant cell**:

```
issuer well   −G          the −supply account
fee well       0          starts empty, accumulates fee MOVES
player grant  +G          named by genesis.json `player_grant`
genesis_moves [ issuer → player_grant, G ]
              Σ balances = 0
```

Value never appears from nowhere: the well goes negative by exactly what the grant
receives, and both `dregg-node genesis` and the deployment verifier refuse a
descriptor whose column does not sum to zero. The grant cell commits its ML-DSA-65
half, so it can actually author hybrid-signed turns (a classical-only genesis cell
is refused `pq-identity-not-enrolled`).

The manifest **declares** the issuance: a funded descriptor emits
`"generic_genesis_value_issued": true`, and the binding is enforced **both ways** —
a funded genesis under a zero-issuance policy is refused, and a policy claiming
issuance over an empty genesis is refused. Because `policy_sha256` feeds
`deployment_digest`, a funded deployment has a different identity from an empty one
and a follower pinned to the old digest refuses it rather than reinterpreting it.

**⚑ Custody — the grant key is DRAWN, not derived.** `bundle/player-grant.key` is 32
bytes from the OS CSPRNG, written `0600` beside the validator seeds, exactly like a
`node-N.key`. **Nothing published determines it**: not `bundle/genesis.json`, not
`poa-devnet.json`, not the follower package. The descriptor carries only the grant
*cell id* and the grant cell's ed25519/ML-DSA *public* keys.

That file is therefore the **sole copy of the key that spends the grant**:

- **Back it up** like a validator seed. There is no re-derivation — lose it and the
  grant is stranded on-chain forever, and the only remedy is a re-genesis.
- **Never distribute it.** It is not part of the follower package and not part of
  what an operator receives; copying it is handing over the grant.
- `scripts/poa-devnet.sh genesis` re-checks it: present when `POA_PLAYER_GRANT > 0`,
  absent when `0`, a 32-byte regular file, mode `600`.

<details>
<summary>⚑ Flag day 2026-08-07 — what this replaced, and why the wells did not change</summary>

Until 2026-08-07 the grant seed was
`auxiliary_genesis_key("dregg-poa-player-grant-key-v1", domain, federation_id)`, and
**both** of those inputs are public — the domain is a compile-time constant and the
federation id is printed in the descriptor every follower pins. So the seed was a pure
function of published data: **anyone who could read `genesis.json` could recompute
`player-grant.key` and spend the grant.** It was bearer value for the whole world,
bounded only by `G`.

`issuer-well.key` and `fee-well.key` keep that exact derivation, and it is sound for
them: a well cannot author a turn (the issuer well's balance is negative and `execute`
refuses a negative-balance agent outright), so recomputing a well key buys nothing,
while reproducing the well cell ids from the descriptor alone is load-bearing for
verification. The grant differs in the one way that decides the question — it holds
**spendable** value. The custody model was carried over from the wells by an
instruction that never priced that difference.

**The old shape now refuses to load.** `dregg_node::genesis::refuse_derivable_player_grant`
recomputes the derivable grant cell from a descriptor's own `deployment_domain` and
`federation_id` and rejects any descriptor whose `player_grant` matches it —
run by `dregg-node genesis` over the exact bytes it is about to write, and by
`complete_boot_recovery` over the exact bytes a node reads, where `Err` means refuse to
serve. A pre-flag-day funded PoA bundle is not reinterpreted; it is re-genesised.
Descriptors that issue no grant (the legacy devnet profile, the zero-issuance PoA
profile, and the live `poa/deployments/epoch-1/` bundle) are untouched.

Held red by `node/src/genesis.rs`'s `custody` tests: the wells must reproduce byte-exact
from each descriptor's own public coordinates, and the grant must **miss** under the
same derivation.
</details>

Per-player custody — grants against keys the players bring — is still a real design
change rather than a bigger number here; what changed is that the shared pool's key is
no longer public.

`POA_PLAYER_GRANT=0` opts out explicitly, prints a warning, and produces the chain
that cannot settle.

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
`bundle/node-N.key`, and do **not** copy `bundle/player-grant.key`: the rest of
`bundle/` is the provisioning archive and contains all three validator seeds
**and the sole copy of the grant key**. Each operator receives exactly one
`node.key` and no grant key at all. On each destination host, print its command with that host's API
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

## Install the Lean-emitted Signal head

Signal authority is initialized by a separate, one-shot operator ceremony; it
is not hidden inside generic node startup. Run it against each PoA node data
directory before that store has finalized an ordinary turn:

```sh
"$POA_BIN" init-poa-signal \
  --data-dir "$POA_ROOT/nodes/node-0" \
  --deployment-manifest "$POA_ROOT/poa-devnet.json" \
  --genesis "$POA_ROOT/bundle/genesis.json" \
  --main-data-dir "$POA_MAIN_DATA_DIR" \
  --poag1-manifest "$PWD/poa/artifacts/poag1/manifest.json" \
  --content-envelope "$PWD/poa/artifacts/poag1/manifest.sig.json" \
  --curator-key-pin "$PWD/poa/config/curator-key.json" \
  --expected-content-epoch 1 \
  --expected-activation-counter 10
```

⚠ The counter is a LIVE value, not a constant of this document. It is
`poa/artifacts/poag1/manifest.sig.json`'s `counter`, and every ceremony bumps it —
this line said `2` until 2026-08-09, so an operator running it verbatim got a
counter refusal and no hint that the doc, rather than their kit, was wrong. Read
the value out of the envelope you are authenticating before you run this.

The command retains and hashes the exact manifest/genesis bytes it authenticated,
rederives the hybrid Ed25519+ML-DSA federation id, and verifies the immutable
production policy, zero demo economy, canonical topology/operator env, and
main-network identity/storage isolation before calling Lean. Lean v2 binds the
exact deployment-manifest and policy digests into the deployment digest persisted
in the head. Consequently a byte-different manifest over the same genesis is a
different authority image, not an idempotent retry. The command authenticates
every POAG1 artifact and detached signature, calls the named Lean NetworkGenesis
export, and atomically installs its exact config/Canon bytes. A different head,
any prior PoA authority/history, a nonempty generic commit log, tuple drift, or a
missing Lean export refuses; the command never resets a database.

Every later node boot that finds a persisted PoA head requires explicit
`POA_DEPLOYMENT_MANIFEST` and `POA_MAIN_DATA_DIR` environment paths. Startup
re-verifies the exact manifest, policy, hybrid committee, main-network isolation,
operator env, and the precise genesis bytes already consumed by the runtime,
then compares the resulting deployment digest with the persisted head before any
Signal finality can run. Generic nodes with no PoA head require neither variable.

## Follower-first participation

Anyone can make a fresh identity, pin the public descriptor, and verify the
lace before receiving voting authority. Copy the checked package to a writable,
private runtime directory; never generate a follower key inside the repository:

```sh
cp -R poa/deployments/epoch-1 "$HOME/path-of-angels/operator-package"
export POA_ROOT="$HOME/path-of-angels/operator-package"
export POA_MAIN_DATA_DIR="$HOME/.dregg"
export POA_BIN="$HOME/bin/dregg-node-poa"

scripts/poa-devnet.sh package-verify
# If the content-named release image has been imported locally:
scripts/poa-devnet.sh image-verify dregg-node:poa-candidate-a9858c0298fa5517
scripts/poa-devnet.sh follower-init deck-447
scripts/poa-devnet.sh follower-command deck-447 100.64.0.3:9423 100.70.0.44
# Once a follow-capable release is resealed, run the printed `join --follow-only`.
scripts/poa-devnet.sh follower-status deck-447 100.70.0.44
scripts/poa-devnet.sh follower-readiness deck-447 100.70.0.44
```

The checked epoch-1 receipt pins binary `a9858c…`, built before
`join --follow-only` existed. Its lock therefore records
`proposal_neutral_follow=false`. `package-verify`, image verification, and
offline identity initialization remain useful, but `follower-command`,
`follower-run`, and `follower-readiness` refuse before network traffic. Do not
edit that boolean: the verifier binds it to the release receipt. The next
candidate must build the source policy, pass the node and package gates, emit a
receipt with `proposal_neutral_follow=true`, and reseal the lock before these
commands become a live sync path.

`package-verify` hashes `POA_BIN` before it can create or read a follower key.
`image-verify` derives the engine-independent ordered-RootFS/config identity
from `docker image inspect`; a matching host-local Docker image ID is neither
required nor sufficient. A release-locked follower may dial only a bootstrap
peer named by the package.

`follower-status` is diagnostic but still refuses a wrong federation, wrong
local identity, Rust producer, disabled full-turn proving, malformed committee,
or leaked private-activity counters. `follower-readiness` additionally requires
a receipted proposal-neutral binary, a healthy synced lace, a peer, history,
and no unratified Join proposal authored by the follower. A key already admitted
to the finalized committee is allowed; `--follow-only` suppresses only the
non-member proposal and does not turn a validator into a non-voter.

The candidate can inspect `/api/membership`.  A current operator can open the
same proposal explicitly and later approve its exact proposal block:

```sh
scripts/poa-devnet.sh propose deck-447 0
scripts/poa-devnet.sh approve <proposal-block-hex> 0
```

Proposing is not admission.  Only finalized current-committee votes change the
live committee.

### What is trustless, and what is not

The package is an authenticated starting-point obligation: obtain its Git
revision or lock digest through a channel you trust. From the exact pinned
genesis, the follower cryptographically verifies the history it receives and
does not trust the bootstrap peer's account of that history. The release
receipt and repository lock attest which source/image/binary was deployed; they
do not make source provenance independent of the release operator.

Admission is still semitrusted and separate from observation. A current
operator explicitly opens a proposal for a willing follower, and the current
committee manually decides membership. A readiness report therefore always
prints `admission=committee-ratified-manual-v1` and
`objective_f4_admission_live=false`, even after the follower becomes a voter.

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

This global `readiness` command is deliberately different from
`follower-readiness`: the latter proves that a non-voting node is correctly
verifying without applying for admission; it does not turn a later manual
admission act into objective F-4 admission.

## Verification

The deployment-policy tests are fast and do not synthesize PQ keys:

```sh
node --test scripts/tests/poa-devnet-manifest.test.mjs
node --test scripts/tests/poa-follower-package.test.mjs
bash -n scripts/poa-devnet.sh
node --check scripts/poa-devnet-manifest.mjs
node --check scripts/poa-follower-package.mjs
```

The node-side domain-key tests are narrow:

```sh
cargo nextest run -p dregg-node -E 'test(/deployment_domain/)'
```

The player-grant custody property — the wells reproduce from public data, the grant
never does — runs two real ceremonies and grades their bundles:

```sh
cargo nextest run -p dregg-node -E 'test(/custody::/)'
```

For a live mesh, `health` additionally requires the manifest federation id at
`/api/membership`, full consensus mode, the Lean producer, full-turn proving,
and absence of public private-volume counters.
