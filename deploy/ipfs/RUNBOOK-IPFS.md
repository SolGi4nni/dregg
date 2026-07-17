# RUNBOOK — kubo on hbox (the IPFS transport for the dregg join)

The join itself is code, in-tree and tested in-process: `dregg-ipfs` (a dregg blake3
commitment IS a CIDv1 blake3 address — CID codec, verified UnixFS file+dir walks,
CAR v1, Kubo/gateway/pinning clients over an injected transport) and
`ugc-dregg::ipfs` (publish/fetch a universe with the UniverseId re-derived from
fetched content). This runbook is the ops half: a kubo daemon on hbox that gives
those clients a real node to talk to.

**Status: reviewed-go.** Everything below the smoke section is exercised in
`cargo test -p dregg-ipfs -p ugc-dregg` against in-process transports; the LIVE
round-trip against a running daemon is untested until an operator runs the smoke
steps. The honest reviewed-go list:

- a live `ipfs daemon` accepting `block/put` / `block/get` / `pin/add` from
  `KuboClient` over `StdHttpPost` (the RPC *formatting* is pinned by tests over a
  recording transport; the daemon's acceptance is not),
- a live gateway `?format=raw` read (`GatewayClient`),
- public-gateway retrievability (DHT provide + propagation),
- byte-exact CID parity between our UnixFS builder and a stock `ipfs add`
  (our DAGs are valid and self-verifying; go-ipfs's exact chunk boundaries are a
  different layout — commit the CID you pinned, not the one you guessed),
- the `kubo-hbox.service` unit surviving install + reboot (its banner comes off
  after that is observed once).

## 1. Install kubo

On hbox (user install, no root — matches the user-unit):

```sh
KUBO_VER=v0.29.0   # or current; check https://dist.ipfs.tech/kubo/
ARCH=$(uname -m | sed 's/x86_64/amd64/; s/aarch64/arm64/')
curl -fsSL "https://dist.ipfs.tech/kubo/${KUBO_VER}/kubo_${KUBO_VER}_linux-${ARCH}.tar.gz" \
  | tar -xz -C /tmp
mkdir -p ~/.local/bin
install /tmp/kubo/ipfs ~/.local/bin/ipfs
~/.local/bin/ipfs version
```

## 2. Init the repo the unit expects

The unit sets `IPFS_PATH=%h/dregg-ipfs` and refuses to start on an uninitialized
repo. Init and configure exactly this:

```sh
export IPFS_PATH=~/dregg-ipfs
ipfs init --profile=server

# Loopback-only RPC + gateway (the unit's contract: nothing listens off-box).
ipfs config Addresses.API /ip4/127.0.0.1/tcp/5001
ipfs config Addresses.Gateway /ip4/127.0.0.1/tcp/8080

# Bounded ConnMgr: swarm stays on (that is what makes pinned CIDs fetchable from
# other nodes) but connection count is capped — hbox co-hosts builds/prover.
ipfs config --json Swarm.ConnMgr '{"Type":"basic","LowWater":64,"HighWater":256,"GracePeriod":"30s"}'

# Bound the repo so --enable-gc has a target.
ipfs config Datastore.StorageMax 20GB
```

(`--profile=server` disables local-network discovery — hbox is on a tailnet; we do
not want mDNS probing it.)

## 3. Install the unit + linger

```sh
mkdir -p ~/.config/systemd/user
cp deploy/ipfs/kubo-hbox.service ~/.config/systemd/user/
systemctl --user daemon-reload
systemctl --user enable --now kubo-hbox
loginctl enable-linger "$USER"   # survives logout/reboot — same as the games units
systemctl --user status kubo-hbox
```

## 4. How dreggnet surfaces reach it

Anything on hbox that publishes/fetches over the join sets:

```sh
DREGG_IPFS_API=http://127.0.0.1:5001       # KuboClient / StdHttpPost (plain HTTP, loopback)
DREGG_IPFS_GATEWAY=http://127.0.0.1:8080   # GatewayClient trustless ?format=raw reads
```

The RPC is unauthenticated and stays loopback-only; a remote or TLS transport is a
caller-supplied `HttpPost` impl across the same seam, never a config flip here.

## 5. Smoke steps (these retire "reviewed-go")

a. **Daemon answers:**

```sh
curl -fsS -X POST http://127.0.0.1:5001/api/v0/version && echo
```

b. **Blake3 CID alignment, raw block:** pin bytes with the exact flags
`KuboClient::put_raw` sends and confirm the returned CID is our alignment CID
(begins `bafk…`, blake3 multihash):

```sh
CID=$(echo -n 'dregg blake3 alignment' | ipfs add -Q --cid-version=1 --hash=blake3 --raw-leaves --pin=true)
echo "$CID"
```

c. **Pin a universe + verified fetches (RPC and local gateway)** — the real join,
driven by the in-tree smoke driver (publishes a deterministic daily universe, then
fetch-verifies it back through both the block API and the gateway, re-deriving the
UniverseId from the fetched content):

```sh
cargo run -p ugc-dregg --example ipfs_smoke
```

d. **Fetch through the local gateway by hand** and confirm byte identity:

```sh
curl -fsS "http://127.0.0.1:8080/ipfs/${CID}?format=raw" -H 'Accept: application/vnd.ipld.raw' \
  | ipfs add -Q --only-hash --cid-version=1 --hash=blake3 --raw-leaves
# prints ${CID} again: the fetched bytes re-derive the same content address
```

e. **Fetch through a PUBLIC gateway by CID** (propagation can take minutes; the
daemon must stay up so the DHT can be provided):

```sh
curl -fsSL "https://ipfs.io/ipfs/${CID}" | ipfs add -Q --only-hash --cid-version=1 --hash=blake3 --raw-leaves
# same CID again — a stranger's gateway served bytes that re-witness against the
# same blake3 commitment. (ipfs_smoke prints the equivalent URL for the universe
# payload CID.)
```

Note: public gateways serve raw blake3 blocks fine (the CID carries its own hash
function); a gateway that refuses blake3 is answered by pinning to a second node
and fetching from there instead — the verification never depends on which node
served the bytes.

f. **Durability:** reboot hbox; `systemctl --user status kubo-hbox` shows the unit
came back and `ipfs pin ls --type=recursive | head` still lists the pins.

## 6. What this deployment is NOT

- Not public: RPC and gateway bind loopback; no funnel is configured here.
- Not a pinning-durability story: one hbox node keeps content exactly as durable as
  hbox. Durable third-party pinning goes through `PinningServiceClient` (the IPFS
  Pinning Service API) with a provider token — the client exists and is
  format-tested; picking/paying a provider is an ember decision.
- Not a TLS deployment: `StdHttpPost` is plain-HTTP loopback by design; anything
  off-box supplies its own TLS-capable transport across the same `HttpPost` seam.
