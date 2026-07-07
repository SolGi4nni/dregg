# Deploying drorb (homelab v0.1)

drorb is a verified network orchestrator: a `Bytes → Bytes` proven-correct core
(compiled to a static library) driven by a native Rust dataplane that owns the
sockets. This directory is the operator's guide to running it as the verified
server in front of real services.

- [`drorb.service`](./drorb.service) — a hardened systemd unit.
- This README — the config format, a worked homelab example, the environment
  variables, how to run it (bare and under systemd), and the known caveats.

---

## The config format

The operator config is a small line-oriented text file. The proven parser
(`Dsl.Config.parseChars`, parse-soundness theorem `Dsl.Config.parse_render`)
reads it **once at boot** and denotes it onto the proven serve pipeline.

The first four lines are required, in order:

```
listener <addr> <port>
pool <name> <lbPolicy>
l4 <none|tcp|udp>
tls <0rtt|no0rtt>
```

- `listener` — the bind address and port the deployment advertises.
- `pool` — the reverse-proxy upstream pool name and the load-balancing policy
  the proven dial runs over it. `<lbPolicy>` is one of:
  `roundRobin`, `leastConn`, `wleastConn`, `ipHash`, `stickyCookie`, `rendezvous`.
- `l4` — `none` for a plain HTTP listener, or `tcp`/`udp` for a layer-4
  passthrough over the pool.
- `tls` — the 0-RTT / early-data toggle of the listener's TLS profile
  (`0rtt` enables early data, `no0rtt` disables it).

Then **zero or more** `route` lines declare the route table (when any are
present they replace the built-in demo routes; with none, the default table is
kept verbatim). Each is one of:

```
route <pattern> static                 # serve the embedded static-file handler
route <pattern> proxy <pool>           # reverse-proxy to the named pool
route <pattern> redirect <status> <location>   # a 3xx redirect
route <pattern> respond <status> <body>        # a fixed local response
```

- `<pattern>` — a path pattern. A trailing `*` is a prefix match
  (`/static/*`); otherwise it is an exact match (`/health`).
- Tokens are whitespace-separated and individually contain **no spaces or
  newlines** (so a `respond` body is a single word/token, e.g. `ok`).
- **A trailing newline is fine.** The parser tolerates a trailing newline and
  blank lines — every editor adds a final `\n`, and the config still parses
  (it does not silently fall back to the demo table).

---

## Worked example — a homelab front door

`/etc/drorb/drorb.cfg`:

```
listener 0.0.0.0 8080
pool app leastConn
l4 none
tls no0rtt
route /static/* static
route /api proxy app
route /health respond 200 ok
route /old redirect 301 /new
```

This config **parses** (verified: the proven core reports
`PARSED ... lb_policy=1, 4 route(s)` at boot). It declares:

- a **static site** under `/static/*` (the embedded static-file handler);
- a **reverse-proxy** route `/api` over the `app` pool, load-balanced with
  `leastConn`; the live upstreams are supplied by `DRORB_PROXY_BACKENDS`
  (below), and the proven policy picks among them;
- a **health** endpoint `/health` answering `200 ok` locally;
- a **redirect** at `/old`.

Run it with the live upstreams and the HTTPS front door wired:

```sh
sudo useradd --system --no-create-home --shell /usr/sbin/nologin drorb   # once

export DRORB_CONFIG=/etc/drorb/drorb.cfg
export DRORB_PROXY_BACKENDS=0=127.0.0.1:9401,1=127.0.0.1:9402   # the two backends
export DRORB_TLS_LISTEN=0.0.0.0:443                              # HTTPS front door
export DRORB_TLS_CERT=/etc/drorb/cert.der                       # Ed25519 default leaf
export DRORB_TLS_SEED=/etc/drorb/seed.bin
export DRORB_TLS_ECDSA_CERT=/etc/drorb/ecdsa-cert.der           # so curl/browsers connect
export DRORB_TLS_ECDSA_KEY=/etc/drorb/ecdsa-key.bin
export DRORB_TLS_RSA_CERT=/etc/drorb/rsa-cert.der               # RSA-PSS clients
export DRORB_TLS_RSA_N=/etc/drorb/rsa-n.bin
export DRORB_TLS_RSA_E=/etc/drorb/rsa-e.bin
export DRORB_TLS_RSA_D=/etc/drorb/rsa-d.bin
export DRORB_ACCESS_LOG=/var/log/drorb/access.log

/opt/drorb/dataplane --bind 0.0.0.0:8080
```

What serves where (see the caveats — this split is real):

- The **HTTPS front door** (`DRORB_TLS_LISTEN`) terminates TLS 1.3 in-process
  over the verified handshake + record layer and serves each decrypted request
  through the proven core — static, redirect, respond, and other in-core routes.
- **Live reverse-proxy dialling** (opening a real socket to a real backend) is
  wired on the **plaintext** HTTP/1.1 listener for the `/api` pool via
  `DRORB_PROXY_BACKENDS`. Point your HTTPS front door or another terminator at
  the plaintext listener for TLS-fronted proxying.

A couple of requests against the plaintext listener, and the access log they
produce:

```
$ curl -s http://127.0.0.1:8080/health        # -> ok
$ curl -s http://127.0.0.1:8080/api            # -> forwarded to a live backend
```
```
ts=2026-07-07T01:12:54.861169Z client=127.0.0.1 method=GET path=/api status=200 backend=127.0.0.1:9401 bytes=127 dur_us=883
ts=2026-07-07T01:12:11.766024Z client=127.0.0.1 method=GET path=/health status=200 backend=- bytes=517 dur_us=343
```

---

## Environment variables

| Variable | Meaning |
|---|---|
| `DRORB_CONFIG` | Path to the operator config file. Parsed at boot by the proven core, and RE-parsed on `SIGHUP` (see [Runtime reconfiguration](#runtime-reconfiguration-sighup)). If unset or the file cannot be parsed, the built-in default deployment runs. |
| `DRORB_ADMIN_LISTEN` | Bind the operator admin surface on this `HOST:PORT` (or bare `PORT` → `127.0.0.1`). Unset ⇒ no admin listener. Serves `GET /metrics` + `GET /healthz`; keep it on a loopback / trusted interface. |
| `DRORB_BIND` | Plaintext HTTP/1.1 bind `HOST:PORT` (or bare `PORT` → `127.0.0.1`). The `--bind` argument overrides it. Default `127.0.0.1:8080`. |
| `DRORB_TLS_LISTEN` | Bind an additional TLS 1.3 HTTPS front door on this `HOST:PORT`. Unset ⇒ no HTTPS listener. |
| `DRORB_TLS_CERT` | DER end-entity certificate — the pool's **Ed25519** default. Default `conformance/tls/cert.der`. |
| `DRORB_TLS_SEED` | 32-byte RFC 8032 Ed25519 signing seed for that cert. Default `conformance/tls/seed.bin`. |
| `DRORB_TLS_ECDSA_CERT` / `DRORB_TLS_ECDSA_KEY` | Optional **ECDSA-P256** leaf (DER) + its 32-byte big-endian signing scalar. Presented to clients offering `ecdsa_secp256r1_sha256`. Default `conformance/tls/ecdsa-cert.der` / `ecdsa-key.bin` (absent ⇒ skipped). |
| `DRORB_TLS_RSA_CERT` / `DRORB_TLS_RSA_N` / `DRORB_TLS_RSA_E` / `DRORB_TLS_RSA_D` | Optional **RSA-PSS-2048** leaf (DER) + big-endian modulus / public exponent / private exponent. Presented to clients offering `rsa_pss_rsae_sha256`. Default `conformance/tls/rsa-cert.der` / `rsa-{n,e,d}.bin` (absent ⇒ skipped). |
| `DRORB_TLS_ECDSA_SNI` / `DRORB_TLS_RSA_SNI` | Optional **SNI host binding** (RFC 6066 §3): bind the ECDSA / RSA pool entry to this host name. It is then presented *only* to a ClientHello whose `server_name` matches (proven `chooseCert_honors_sni`); other names / no-SNI fall to the name-agnostic entries. Keep at least one entry unbound so non-matching clients still get a leaf. Unset ⇒ that entry serves any name. |
| `DRORB_TLS_EARLY_DIR` | Opt into **0-RTT / early data** (RFC 8446 §4.2.10). Set to a writable directory used as the single-use anti-replay register (one file per ticket identity). Issued tickets then advertise `max_early_data`; a fresh 0-RTT offer is accepted, a replay is rejected. Unset ⇒ **session resumption only** (tickets issued, 0-RTT refused / trial-skipped). |
| `DRORB_ACCESS_LOG` | Opt-in access log. `1` (or `stderr`) writes to stderr/journal; any other value is a file path (append). Unset/`0` ⇒ off. |
| `DRORB_PROXY_BACKENDS` | Live reverse-proxy pool for `/api`: `id=host:port` entries, comma-joined (e.g. `0=127.0.0.1:9401,1=127.0.0.1:9402`). A background health loop probes each. |
| `DRORB_L4_LISTEN` / `DRORB_L4_UDP` | Bind a raw layer-4 (TCP/UDP) passthrough over the proxy pool. |
| `DRORB_UDP` / `--no-udp` | QUIC/HTTP-3 UDP bind (defaults to the same `HOST:PORT` as the TCP bind); `--no-udp` disables it. |
| `DRORB_IO` / `--io` | IO path: `auto` (io_uring on Linux, blocking elsewhere), `blocking`, or `uring`. |
| `DRORB_SHARDS` / `--shards` | io_uring shard count (Linux). |

---

## Running it

### Bare

```sh
# Build the proven static library, then the dataplane host that links it.
bash ffi/build-dataplane-lib.sh
( cd crates/dataplane && cargo build --release )

DRORB_CONFIG=/etc/drorb/drorb.cfg \
DRORB_ACCESS_LOG=1 \
./target/release/dataplane --bind 0.0.0.0:8080
```

SIGINT (Ctrl-C) stops the accept loop cleanly.

---

## Runtime reconfiguration (SIGHUP)

The operator config is not frozen at boot. Send the running process **`SIGHUP`**
and it re-reads `DRORB_CONFIG`, re-parses it through the **same proven parser**
(`Dsl.Config.parseChars` — the parse that ran at boot), and, **only if it
parses**, atomically swaps in the new deployment for every subsequent request —
**without a restart and without dropping a connection**.

```sh
# edit /etc/drorb/drorb.cfg, then:
kill -HUP "$(pidof dataplane)"      # or: systemctl reload drorb
```

- **New connections use the new config; in-flight requests finish under the old
  one.** The swap is a single atomic publish of the parsed deployment. A request
  already in flight holds its own snapshot and completes under the config it
  started on; the next request picks up the new generation. This is the
  connection-draining discipline proved in `Drain.lean` / `DrainCorrect.lean`
  (`DrainContract`): once the reload fires, no new work is admitted under the old
  generation, and every in-flight request is allowed to complete — the old
  generation is "drained" exactly when its last in-flight request finishes. The
  untrusted host shell executes that proven decision; it does not re-decide it.
- **A bad config is a no-op (fail-safe).** If the new file cannot be read or the
  proven parser rejects it, the running config is **kept** and a line is logged:

  ```
  dataplane: SIGHUP reconfig REJECTED — keeping the running config (fail-safe): did not parse (proven parser returned none)
  ```

  A successful reload logs the new generation:

  ```
  dataplane: SIGHUP reconfig APPLIED — config generation 2; new connections use gen 2, …
  ```

The current generation is reported by `/metrics` as `drorb_config_generation`
(see below): it starts at 1 for the boot config and increments on each applied
reload.

---

## Metrics and health (the admin surface)

Set `DRORB_ADMIN_LISTEN` (e.g. `9090`, or `127.0.0.1:9090`) to bind a small
**admin listener on a port separate from the serve listeners** — keep it on
loopback or a trusted management interface. It answers two routes:

- **`GET /metrics`** — operational counters in Prometheus text format;
- **`GET /healthz`** — `200 ok` while serving, `503` once shutdown has begun.

```sh
DRORB_CONFIG=/etc/drorb/drorb.cfg \
DRORB_ADMIN_LISTEN=127.0.0.1:9090 \
./target/release/dataplane --bind 0.0.0.0:8080

$ curl -s http://127.0.0.1:9090/healthz          # -> ok
$ curl -s http://127.0.0.1:9090/metrics
drorb_requests_total 1
drorb_responses_total{class="2xx"} 1
drorb_responses_total{class="3xx"} 0
drorb_responses_total{class="4xx"} 0
drorb_responses_total{class="5xx"} 0
drorb_response_bytes_total 504
drorb_active_connections 0
drorb_backend_requests_total{backend="127.0.0.1:9401"} 3
drorb_config_generation 1
drorb_reloads_applied_total 0
drorb_reloads_rejected_total 0
drorb_draining 0
```

The counters are **untrusted-shell observability**: the host counts what it
already has in hand at each served response (status class, bytes, the dialled
proxy backend) from the serve loop — outside the proven core. No counter feeds
any request decision. `drorb_config_generation`, `drorb_reloads_applied_total`,
and `drorb_reloads_rejected_total` track the SIGHUP reconfig above.

### Under systemd

1. Install the binary and data under `/opt/drorb` (the `dataplane` binary, and
   for the HTTPS front door the cert/seed), the config under `/etc/drorb/`, and
   create the log dir:

   ```sh
   sudo useradd --system --no-create-home --shell /usr/sbin/nologin drorb
   sudo install -d -o drorb -g drorb /opt/drorb /etc/drorb /var/log/drorb
   sudo install -m 0755 target/release/dataplane /opt/drorb/dataplane
   sudo install -m 0640 -o drorb -g drorb your.cfg /etc/drorb/drorb.cfg
   ```

2. Generate the certificate pool (see below) and place the material under
   `/etc/drorb/` (Ed25519 `cert.der` + `seed.bin`; optionally the ECDSA-P256 and
   RSA-PSS leaves so curl/browsers connect).

3. Install and start the unit:

   ```sh
   sudo cp deploy/drorb.service /etc/systemd/system/drorb.service
   sudo systemctl daemon-reload
   sudo systemctl enable --now drorb
   journalctl -u drorb -f
   ```

The shipped unit binds `:80` plaintext and `:443` HTTPS via
`CAP_NET_BIND_SERVICE` (no root), restarts on failure, and runs under a locked-
down sandbox (`ProtectSystem=strict`, `NoNewPrivileges`, a `@system-service`
syscall filter, and a read-only filesystem except `/var/log/drorb`). Edit the
`Environment=` lines to match your config.

### The TLS certificate pool

The front door serves a **certificate pool** and presents the one the verified
`chooseCert` selects for each client's `signature_algorithms` (RFC 8446 §4.4.2.2
/ §4.2.3):

- an **Ed25519** default leaf (`cert.der` + `seed.bin`), and — when supplied —
- an **ECDSA-P256** leaf (`ecdsa-cert.der` + `ecdsa-key.bin`), preferred when the
  client offers `ecdsa_secp256r1_sha256`, and
- an **RSA-PSS-2048** leaf (`rsa-cert.der` + `rsa-{n,e,d}.bin`), for clients that
  offer `rsa_pss_rsae_sha256`.

Generate self-signed material with OpenSSL: `conformance/tls/gen-cert.sh` makes
the Ed25519 default (leaf + CA + seed, SAN `localhost`/`127.0.0.1`) and
`conformance/tls/gen-pool.sh` makes the ECDSA-P256 and RSA-PSS leaves plus the
raw signing-key material in the byte form the verified HACL* signer reads. Adapt
their subject/SAN for your host, then copy the files to `/etc/drorb/`.

The default (ECDSA/RSA-preferring) pool means **curl, LibreSSL, and browsers
connect** — they need an ECDSA or RSA leaf and reject an Ed25519-only server:

```sh
openssl s_client -connect your.host:443 -servername your.host </dev/null
#   ... Peer signature type: ecdsa_secp256r1_sha256 / Protocol: TLSv1.3
curl -k https://your.host/health          # -> 200 ok

# Force a specific cert type (each is served by chooseCert):
openssl s_client -connect your.host:443 -sigalgs rsa_pss_rsae_sha256 </dev/null
openssl s_client -connect your.host:443 -sigalgs ed25519 </dev/null

# Or pin the issuing CA of the Ed25519 default (convert DER→PEM):
openssl x509 -inform der -in conformance/tls/chain.der -out /tmp/drorb-ca.pem
curl --cacert /tmp/drorb-ca.pem https://your.host/health
```

### SNI selection, ALPN, resumption, and 0-RTT

The front door drives these over the same proven `serverStep` the testssl-A+
conformance oracle uses:

```sh
# SNI cert selection — bind the ECDSA entry to a host (DRORB_TLS_ECDSA_SNI=ecdsa.host):
openssl s_client -connect your.host:443 -servername ecdsa.host </dev/null
#   ... Peer signature type: ecdsa_secp256r1_sha256   (the SNI-bound ECDSA leaf)
openssl s_client -connect your.host:443 -servername other.host </dev/null
#   ... Peer signature type: rsa_pss_rsae_sha256      (the name-agnostic entry)

# ALPN — the front door advertises http/1.1:
openssl s_client -connect your.host:443 -alpn h2,http/1.1 </dev/null
#   ... ALPN protocol: http/1.1

# Session resumption — a NewSessionTicket is issued; a later offer resumes:
openssl s_client -connect your.host:443 -sess_out /tmp/s.pem </dev/null   # New,
openssl s_client -connect your.host:443 -sess_in  /tmp/s.pem </dev/null   # Reused,

# 0-RTT / early data — opt in with DRORB_TLS_EARLY_DIR=/var/lib/drorb/early:
printf 'GET / HTTP/1.1\r\nHost: x\r\n\r\n' > /tmp/e.req
openssl s_client -connect your.host:443 -sess_in /tmp/s.pem -early_data /tmp/e.req
#   ... Early data was accepted   (first use); "rejected" on a replay of the ticket
```

h2-over-TLS is a follow-on: the front door advertises and serves the HTTP/1.1
pipeline (`drorb_serve`); the plaintext listener carries the h2c → real-H2 path.

---

## Known caveats (v0.1)

- **Self-signed default certificates.** The shipped material is self-signed
  (SAN `localhost`/`127.0.0.1`); use `-k` / import the CA for a smoke test, and
  supply your own CA-issued ECDSA/RSA/Ed25519 leaves in production. The verified
  handshake presents whichever the client's `signature_algorithms` selects — no
  RSA/ECDSA gap remains.
- **Single serve thread ⇒ ~3k rps.** All Lean seams are crossed on one
  runtime-owner thread (the honest single-owner discipline), so throughput is
  bounded (order of a few thousand requests/second on a homelab box). This is
  fine for fronting home services; it is not a CDN edge. The fast, leanc-free
  datapath is the standing performance work, not shipped here.
- **No runtime config reload.** The config is parsed once at boot. To change
  routes/pools, restart the service (`systemctl restart drorb`).
- **The access log covers the plaintext HTTP/1.1 path.** The TLS front door
  serves each whole connection inside the proven core, so per-request host-side
  access logging is emitted for the plaintext listener, not the in-core TLS
  path.
- **Live reverse-proxy dialling is the `/api` pool on the plaintext listener.**
  A `route ... proxy` line is representable in the config and served through the
  proven route table; opening a real socket to a real upstream is wired for the
  `/api` pool via `DRORB_PROXY_BACKENDS`. Front it with the HTTPS listener (or
  another terminator) for TLS-fronted proxying.
