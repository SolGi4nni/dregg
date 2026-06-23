# The self-describing vessel — deos carries its own source

An agent put into deos — a Claude logged into the embedded Hermes, or the cockpit
itself — can already crawl the **runtime**: the cells, the caps, the receipts,
through the reflective object model (`reflect`, the inspectors, the MCP driving
harness). That tells it the live *state*. It does not tell it *what it is*.

To understand what it inhabits, an agent needs the **source** — the Rust, the Lean
(`metatheory/`, especially `CONSTRUCTIVE-KNOWLEDGE.md` and `DREGG-CALCULUS.md`),
the docs that define the system. So deos carries a bundled copy of the dregg source
and exposes it as a read surface from within. It probably needs a bundled copy of
the dregg source itself to have any hope of understanding what it is trapped within.

This is built in two halves: a **source payload** (the carrier) and a **read
surface** (`SourceVessel`).

## 1. The source payload — the carrier

`scripts/pack-dregg-src.sh` assembles the definitional source into a compressed
tarball, `dregg-src.tar.zst`.

- **What it carries.** The files that *define* the system: `.rs`, `.lean`, `.md`,
  `.toml`, `.sh`, `.py`. Nothing else.
- **What it excludes.** All build artifacts — `target/`, `.git/`, `node_modules`,
  the vendored crate caches, `*.crate`, `libdregg_lean.a`, images and binary blobs.
- **How it stays clean.** The packer takes `git ls-files` and filters to the source
  extensions. The tracked set is *already* the no-artifacts set (`.gitignore`
  excludes `target/`, `node_modules`, `*.crate`, `*.zip`, the Lean object caches,
  `metatheory/.lake`, …), so the payload is exactly the definitional corpus with
  zero artifact leakage and zero hand-maintained exclude list.

Measured size (current tree):

| measure | value |
|---|---|
| files | 3,655 definitional source files |
| raw | 76.8 MB (the source that defines the system) |
| packed (`zstd -19`) | ~15.0 MB |
| ratio | ~5.1× |

Tens of MB, not GB — small enough to ship inside the AppImage. The packer also
emits `dregg-src.manifest.txt`, a plain table of contents (the bundled paths) the
vessel can present without unpacking.

## 2. The carrier in the AppImage

The Linux AppImage already bundles the cockpit + a local node. The installers
workflow (`.github/workflows/starbridge-v2-installers.yml`) adds the source payload:

- a **pack step** runs `scripts/pack-dregg-src.sh` into a staging path,
- the **packaging step** copies it into `AppDir/usr/share/dregg-src/dregg-src.tar.zst`,
- a **smoke check** extracts the shipped AppImage and asserts the payload is present
  and holds `metatheory/CONSTRUCTIVE-KNOWLEDGE.md`.

So a shipped image carries cockpit + node + **its own source**.

(The macOS `.app`/`.dmg` jobs build per-arch and do not yet copy the payload into
`Contents/Resources`; the carrier + the runtime reader are platform-agnostic, so
adding the same copy step there is a mirror of the Linux block. The Linux AppImage
is the bundled-source proof today.)

## 3. The read surface — `SourceVessel`

`starbridge-v2/src/source_vessel.rs` is the read surface over the carrier. It is a
**cap-bounded read** over the source root, and nothing more:

- It exposes only `read` / `read_bytes` / `list` / `list_under` / `contains`.
  There is **no write or mutate method** — reading the source grants no
  write-authority over the live system. The bound is in the *type*, not a runtime
  check to forget. An agent holding a `SourceVessel` can learn what it inhabits; it
  cannot use that to change it.
- Every read is **confined** to the vessel root. A requested path is normalized; a
  `..` that would climb above the root (or an absolute path reaching outside the
  source prefix) is refused. The vessel's authority is exactly "the bundled source,
  read-only."

### Finding the carrier at runtime

`SourceVessel::discover()` locates the carrier in order:

1. `$DREGG_SRC_ARCHIVE`, if set (a dev/test/explicit override),
2. next to the executable, the AppImage layout: `<exe_dir>/../share/dregg-src/dregg-src.tar.zst`
   (`AppDir/usr/bin` → `AppDir/usr/share`), plus a couple of sibling fallbacks.

If none is present it returns an error naming the searched paths — the honest "this
build did not ship the source" signal, never a silent empty vessel.

### Reading a source file by path

```rust
let vessel = SourceVessel::discover()?;            // find + index the carrier
let ck = vessel.read("metatheory/CONSTRUCTIVE-KNOWLEDGE.md")?;  // the cap-bounded read
// → the real content of the file that names dregg as a metatheory of
//   constructive knowledge — read from within deos.
```

The carrier (~15 MB) is decoded once into an in-memory path→bytes index, so each
read is a map lookup. The index *is* the cap: there is no handle to anything
outside it.

## 4. The source as read-only cells (the FirmamentFs mount)

The richer surface mounts the source as cells through the **same `FirmamentFs`**
the editor and self-hosting loop use (`deos-zed/src/fs/firmament.rs`), so the source
appears in the reflective image the cockpit inspects — as files that *are* cells.

`source_vessel::seed_into_firmament` (the `firmament` feature) seeds the source
files as file cells under a mount root (e.g. `/dregg-src`), each carrying its
content as genesis state. The mount is read-only: a save against a source cell the
editor holds no edit cap for is refused in-band by the cross-cell cap gate (the
same anti-ghost tooth `firmament.rs` tests). The agent reading the source is a
cap-bounded read; it does not get write-authority over the live system from it.

## 5. Verify by running

The proof is *running*, not compiling:

- **Mechanics** — `source_vessel`'s unit tests build an in-memory `dregg-src.tar.zst`
  carrier (exactly as the packer does), open it through `SourceVessel`, and read a
  source file back by path; they also assert the confinement (a `..` escape is
  refused) and that an empty carrier is refused.
- **Over the real source** — `starbridge-v2/tests/source_vessel_real.rs` runs
  `scripts/pack-dregg-src.sh` to pack the **actual** dregg source, opens the carrier
  through `SourceVessel`, and reads `metatheory/CONSTRUCTIVE-KNOWLEDGE.md` and
  `dregg-lean-ffi/src/lib.rs` — asserting each matches the on-disk source
  byte-for-byte. A real dregg source file is readable from within deos.

## Why this is the right shape

deos is an ocap system: authority is a held capability, never ambient. The vessel
is faithful to that. "Read your own source" is a *read* capability — bounded,
confined, and unable to confer write-authority. An agent can come to understand the
system it is trapped within without that understanding becoming a lever to change
it. The smallest real thing that lets code inside deos read a source file by path,
expressed as the cap it actually is.
