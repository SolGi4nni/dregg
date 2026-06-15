# dregg — the Python SDK

The pyo3 binding for the dregg SDK's two-noun surface:

```python
import dregg

ident = dregg.Identity.from_profile("ember")      # ~/.dregg/profiles, shared with the CLI
receipt = (ident.turn("https://devnet.example")
                .transfer("28c2cba0…", 100)
                .sign()
                .submit())
print(receipt.turn_hash, receipt.has_proof)
```

An unauthorized act is inexpressible: nothing leaves `.sign()` until it is a
real Ed25519-signed canonical `SignedTurn`, and the node ingress verifies it.
The module is fully typed — it ships `dregg.pyi` + a `py.typed` marker, so
IDEs, mypy, and pyright resolve the whole surface.

## The organ nouns

Above the two base nouns sit the **organs** (`docs/ORGANS.md`) — the higher
primitives, each the ergonomic Python face of a node service. The node computes
the per-cell factory descriptors and seal fan-outs the wire layer does not
carry; these clients drive them. The enforcement tooth is the
executor-installed cell program either way.

```python
# §1 Trustline — the bilateral line of credit (operator-gated).
tl = issuer.trustline(node, devnet_key=KEY)
line = tl.open(holder.cell_id, 1000)        # four-turn funded birth
tl.draw(line["trustline"], 250)             # debit the shared counter
tl.status(line["trustline"])                # {line, drawn, remaining, escrow, open, …}

# §4 Channels — the group-key epoch lift (operator-gated).
ch = issuer.channels(node, devnet_key=KEY)
g = ch.create(7, [{"cell": alice.cell_id, "seal_pk": alice_seal_hex}])
ch.remove(g["channel"], bob.cell_id)        # bob darkened in ONE epoch step
for m in ch.messages(g["channel"]): ...     # SSE ciphertext envelopes

# §2 Mailbox — a hosted inbox over the relay (owner-signed).
mb = holder.mailbox("http://relay.example:3100")
mb.subscribe()                              # create your inbox
out = mb.drain(50)                          # each carries a dequeue (custody) proof

# Light-client reads — no identity, no signing.
aq = dregg.AttestedQuery(node)
aq.checkpoint()                             # latest finalized checkpoint (+ qc votes)
aq.turn_proof(turn_hash)                    # full-turn STARK bytes (verify elsewhere)

# Devnet faucet — materialize + fund a hosted cell.
dregg.faucet(node, ident.cell_id, 2000, public_key=ident.public_key)
```

**Honest scope.** Operator-gated organs (trustline, channels) carry the node
operator's credential (`devnet_key=`, else `$DREGG_API_TOKEN`). Sealing
(X25519 → ChaCha20-Poly1305), the per-group seal fan-out, re-running a dequeue
Merkle verifier, and verifying a STARK/threshold signature are **not** done in
this binding — it surfaces the artifacts to verify with the Rust/Lean path. See
`examples/organs.py`.

## DreggDL — the checkable deployment spec (`dregg.deploy`)

Write a dregg capability layout **once**, declaratively (TOML / JSON), and
`check` it for the four static guarantees — conservation, non-amplification,
well-formedness, ring-balance — over the WHOLE declared authority layout BEFORE
submitting, exactly like the Rust `dregg-deploy check` CLI:

```python
import dregg.deploy as deploy

verdict = deploy.check(open("escrow.dregg.toml").read())
if not verdict["pass"]:
    for f in verdict["assurance"]["findings"]:
        print(f"{f['guarantee']}: {f['message']} @ {f['locus']['display']}")
# verdict = {pass, assurance{conservation, no_amplification, wellformed,
#            ring_balance, findings}, factories[], cells[], turn_count}

forest = deploy.lower(toml_text)   # the ordered CallForest the checker consumes
```

`dregg.deploy` is a **thin binding** over the REAL `dregg-deploy` crate: parse →
`Lowered::from_deployment` (name resolution + the ordered `CallForest`) →
`dregg_userspace_verify::analyze`. The lowering, the `CallForest` construction,
and the checks are NOT reimplemented in Python — a deployment audited from
Python is audited by the exact same code as `dregg-deploy check`. An
over-granting deployment FAILs with the located amplification; an unknown row
raises `DreggError` naming it.

## pg-dregg-native — drive pg-dregg from Python (`dregg.pg`)

`dregg.pg` is a thin, well-typed `psycopg`-based binding of the **real** pg-dregg
SQL surface (`docs/PG-DREGG.md`): a Python user connects to a pg-dregg-enabled
PostgreSQL and lets pg-dregg enforce. The model is the spine — **reads are free
SQL; state mutates only through verified turns** — so the surface falls into
exactly that shape. `psycopg` is imported lazily; install it with
`pip install 'dregg[pg]'`.

```python
from dregg import pg

with pg.connect("host=/var/run/postgresql dbname=dregg", token=my_dga1_token) as db:
    # (b) cap-gated reads — only the cells the presented token admits 'read' on.
    for c in db.cell_balances():            # free SQL over dregg.cell_balances, RLS-gated
        print(c.cell, c.balance)
    head = db.chain_head()                  # the receipt hash chain (anti-substitution tooth)

    # (c) a verified write — submit a signed turn through the spine (RLS-gated to
    #     the agents the token admits 'submit' on); the node drains it.
    sid = db.submit_turn(signed_turn_bytes, agent_cell)
    print(db.submission(sid).status)        # pending → executed | refused
```

### (a) Durable verified workflows (`dregg.pg.DurableWorkflow`)

An ordered, named sequence of verified turns, driven durably — **each step a
verified turn, exactly-once across crashes**. The Python face of
`pg_dregg::workflow` (`pg-dregg/examples/subscription_billing.rs` is the
behavioral reference), realized over the **persisted** `dregg.submit_queue` rows
(durability that survives a crash lives in the committed rows, which only the SQL
path reaches):

```python
wf = (db.durable_workflow("monthly-billing")
        .step("charge alice", alice_cell, alice_turn_bytes)
        .step("charge bob",   bob_cell,   bob_turn_bytes))
report = wf.run(db)            # enqueue each (durable), drive to executed | refused
# …process crashes, restarts…
report = wf.resume(db)         # reconciles the persisted queue: skips alice (already
                               # committed), re-drives only the uncommitted tail
print(report.committed, report.skipped)
```

Exactly-once is dual-enforced (the same as the Rust `resume_durable`): a committed
step is skipped by reconciliation (the fast path), and even a stale re-submit is
refused by the node's chain tooth (the backstop). A cancelled subscription is a
`dregg_revoke` — the next charge is refused on the very next turn (instant
revocation, consulted by the `submit_gate` RLS).

**Honest seam.** The durable enqueue, the `submit_gate` RLS, and the crash-resume
reconciliation are **real and enforced by the database engine** (exercised against
live pg18 in `tests/test_pg_workflow.py`). The transition that *executes* a queued
turn (`pending → executed`) is the **node drainer's** job (it runs each turn
through the real verified Lean executor; `docs/PG-DREGG.md` §11.4). Where no node
runs, `dregg.pg.LocalDrainer` stands in for dev/tests — a `dregg_kernel`-role
applicator that resolves the row (and faithfully re-checks revocation) but is NOT
the verified executor. See `examples/pg_durable_workflow.py` for the full
recurring-billing story (cap-gated, instant-revocation, crash-resume) against live
pg-dregg.

## The kernel this module embeds

The extension module links the **verified Lean kernel** (`metatheory/Dregg2`, via
`dregg-lean-ffi`) — the same executor every native dregg binary runs. `dregg.kernel()`
reports it and proves it by driving one transfer through the proved `Exec.recKExec`:

```python
>>> dregg.kernel()
{'lean': True, 'producer': 'lean', 'verified_step_ok': True,
 'verified_step_out': '{"cells":[[1,…45…],[2,…15…]],"ok":1}'}
```

The Lean runtime is initialized once, at `import dregg`, on the importing thread.

## How the link works (shared mode)

A Python extension module is a shared object, and the Lean *static* runtime archives
cannot be linked into one on ELF (`libleanrt.a`'s mimalloc objects use local-exec TLS —
`R_X86_64_TPOFF32` relocations are illegal under `-shared`). So this crate builds with
`DREGG_LEAN_LINK=shared` (set by `.cargo/config.toml`; an env var, not a cargo feature,
so it can never feature-unify onto the native crates):

* `libdregg_lean.a` (the Dregg2 + dependency *module* objects, compiled `-fPIC`) is
  still linked statically — that is the verified kernel itself;
* the Lean **runtime + stdlib** resolve against the toolchain's shared libraries
  (`libleanshared`, `libLake_shared`, and on platforms where the split is real
  `libInit_shared`/`libleanshared_1`/`libleanshared_2`) from `$LEAN_SYSROOT/lib/lean`;
* `build.rs` stamps an rpath to the active elan toolchain's `lib/lean`, so dev builds
  import with no environment setup on the machine that built them.

## Building

Dev build + test (the elan toolchain and `lake` must be on PATH, exactly as for the
rest of the workspace — `./scripts/bootstrap.sh` at the repo root checks everything):

```sh
cd sdk-py
cargo build                  # DREGG_LEAN_LINK=shared via .cargo/config.toml
# maturin develop            # same thing, installed into the active venv
python3 -c 'import dregg; print(dregg.kernel())'
```

Without `maturin`, the built cdylib works directly: copy
`target/debug/libdregg.dylib` (macOS) / `target/debug/libdregg.so` (Linux) to
`dregg.so` somewhere on `sys.path`.

## Wheels (distribution)

The rpath baked by `build.rs` points at the *building* machine's elan toolchain, so a
wheel made from a dev build runs anywhere only if libleanshared is findable. Two
supported stories:

1. **Toolchain-on-host (current):** the host installs the pinned Lean toolchain (elan)
   and, if the toolchain lives somewhere else, points the loader at it:
   `LD_LIBRARY_PATH=$LEAN_SYSROOT/lib/lean` (Linux) /
   `DYLD_LIBRARY_PATH=$LEAN_SYSROOT/lib/lean` (macOS). Build-time override:
   `DREGG_LEAN_SYSROOT=<sysroot>` bakes that rpath instead.
2. **Bundled (self-contained wheels):** graft the shared libraries into the wheel with
   the standard repair tools — `auditwheel repair` (Linux) / `delocate-wheel` (macOS)
   after `maturin build --release`. They rewrite the rpath to the wheel-internal copy.
   Expect large wheels (libleanshared is ~150 MB unstripped); this is the path for
   publishing, not for dev.

## Tests

```sh
python3 -m pytest tests/    # needs the module importable (maturin develop, or copy the cdylib)
```

`tests/test_smoke.py` covers profiles/signing/submit against an in-process mock node,
plus the kernel probe (`test_kernel_is_lean` asserts this build embeds the Lean
kernel — it is *supposed* to fail on a build that silently fell back to Rust).
