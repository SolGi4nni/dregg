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
