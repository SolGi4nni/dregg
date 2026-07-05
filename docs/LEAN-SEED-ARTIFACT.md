# The Lean seed as a release artifact — verified nodes in minutes, not hours

The single biggest barrier to a stranger running a **verified** `dregg-node` is the Lean seed:
`dregg-lean-ffi/libdregg_lean.a`, a ~180 MB native static archive of the compiled verified
executor plus its entire mathlib/batteries/aesop/Qq dependency closure (~6000 objects). It is
**gitignored** (an architecture-native Mach-O/ELF blob — never a repo blob), so a fresh clone that
runs `cargo build` without it silently builds **marshal-only**: `lean_available()==false`, and the
node runs the *un-verified* Rust executor. Regenerating the seed from source is an **hours-long**
cold `lake` bootstrap (it compiles mathlib).

This document describes the mechanism that turns that into a **minutes-long** download: publish a
HEAD-matching seed as a **GitHub release asset**, and fetch it on a fresh clone.

See also `docs/BUILD-LEAN-LINKED-NODE.md` (the build-time story + the `DREGG_REQUIRE_LEAN` gate).

## The pieces

| File | Role |
|------|------|
| `scripts/lean-seed-key.sh` | Computes the seed **provenance + content key** (platform · Lean toolchain · mathlib rev · Dregg2 tree hash) and the canonical asset name. Shared by fetch + publish. |
| `dregg-lean-ffi/lean-seed.pin` | The committed **pointer**: which release `TAG` holds the current seed, and the provenance it was cut from. Rewritten by the publish workflow. |
| `scripts/fetch-lean-seed.sh` | Downloads the platform-native seed asset from the pinned release, **verifies the sha256 + the `dregg_*` exports**, and installs it at `dregg-lean-ffi/libdregg_lean.a`. |
| `.github/workflows/lean-seed.yml` | The **publish** workflow: build the seed on a beefy host, compress, upload the asset + `.sha256` to a release, and bump the pin. |
| `scripts/run-node-10min.sh` | The end-to-end "clone → seed → build → run → verify" convenience path. |

## The seed key (why an asset is HEAD-matching)

A seed archive is valid only for a specific **platform** (Mach-O arm64 ≠ ELF x86_64), **Lean
toolchain** (the runtime/stdlib ABI it links against), **mathlib pin** (its dependency closure),
and **Dregg2 source tree** (the executor slice baked in — used verbatim on the fetch path, where a
fresh clone has no warm `.lake` to re-splice from). `scripts/lean-seed-key.sh` hashes exactly those
into a short key and names the asset:

```
libdregg_lean-<os>-<arch>-<lean-tag>-<key>.a.zst
# e.g. libdregg_lean-Linux-x86_64-v4.30.0-1a2b3c4d5e6f7a8b.a.zst
```

Same key ⇒ interchangeable seed. `fetch-lean-seed.sh` computes the local key, downloads the asset
of that exact name, and **warns loudly** if the committed pin's `DREGG_TREE_HASH` has drifted from
your checkout (a stale seed whose Dregg2 slice predates your source — the closure link may then
need a warm local `.lake`).

## Fetching (the fast path, for everyone)

```sh
# 1. elan + the pinned toolchain must be on PATH (installs in minutes; NO mathlib compile):
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh    # then re-open your shell

# 2. fetch the prebuilt seed for your platform:
./scripts/fetch-lean-seed.sh

# 3. build a VERIFIED node, failing loud on any silent marshal-only degrade:
DREGG_REQUIRE_LEAN=1 cargo build -p dregg-node --release
```

The seed links against the toolchain's Lean runtime; if `lake env` can't be found at build time,
export the sysroot explicitly: `export DREGG_LEAN_SYSROOT="$(cd metatheory && lake env printenv LEAN_SYSROOT)"`.

If no seed release has been cut yet, `fetch-lean-seed.sh` **fails loud** and points you at either a
local `./scripts/bootstrap.sh` (the slow, hours-long path) or cutting a release (below). The
`DREGG_REQUIRE_LEAN=1` gate guarantees you can never *silently* ship a marshal-only node — the
build panics with the exact cause instead. (Confirmed wired: `dregg-lean-ffi/build.rs`
`degrade_guard`, and a `--release` native build defaults the gate ON.)

## Cutting a seed release (needs a beefy build host — "lassie")

Seeding compiles thousands of leanc objects. `metatheory/lakefile.toml` pins mathlib as a
**portable `git`+`rev` dependency**, so `lake` fetches it on any host with no clone-location
assumption — but a stock GitHub-hosted runner still lacks the **hours** (and a prebuilt mathlib
cache). Cut seeds on a **self-hosted beefy host** (David's *lassie*, Linux, 128t/1TB).

### Via the workflow (preferred)

`Actions → Publish Lean seed → Run workflow`, with a `tag` (e.g. `lean-seed-2026-07-05`) and the
self-hosted `runner` label. It runs `bootstrap.sh`, compresses, uploads the asset + `.sha256` to
the release, and commits the pin bump. Run it once **per platform** you want to serve (each
self-hosted host contributes its own native asset to the same tag).

### By hand on lassie — the exact cold-bootstrap recipe (copy-paste)

This is the full ordered command list to cut the **first** seed on a fresh Linux box. Nothing here
depends on a host-specific path — mathlib is git-fetched by lake.

```sh
# 0. Prerequisites (once per box). elan installs in minutes; it does NOT compile mathlib.
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh          # rust (cargo)
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh                  # elan (lake); re-open shell
#   plus: git, zstd, and GitHub `gh` (authed: `gh auth login`) on PATH.

# 1. Clone breadstuffs anywhere (clone LOCATION does not matter — the mathlib pin is git+rev).
git clone git@github.com:emberian/dregg.git breadstuffs
cd breadstuffs

# 2. Cold-bootstrap the verified Lean seed. bootstrap.sh:
#      - reads the mathlib git pin from metatheory/lakefile.toml,
#      - runs `lake exe cache get` to pull mathlib's PREBUILT oleans (minutes, not the hours-long
#        from-source compile),
#      - `lake build`s the Dregg2.Exec.FFI closure,
#      - seeds dregg-lean-ffi/libdregg_lean.a and verifies the FFI kernel round-trips.
#    EXPECTED TIME (honest): with the mathlib cache available this is ~30-90 min on lassie (the
#    leanc compile of the ~6000-object Dregg2+deps closure dominates). If the mathlib prebuilt
#    cache is UNAVAILABLE for this rev, mathlib compiles from source and it is HOURS — this is the
#    one-time cold-boot cost the published seed exists to spare everyone else.
./scripts/bootstrap.sh

# 3. Name + compress + checksum the platform-native seed (asset name encodes os·arch·lean·key).
asset="$(scripts/lean-seed-key.sh --asset)"                             # libdregg_lean-Linux-x86_64-v4.30.0-<key>.a.zst
zstd -q -19 --long=27 -T0 dregg-lean-ffi/libdregg_lean.a -o "$asset"    # ~180 MB → ~20 MB
sha256sum "$asset" > "$asset.sha256"

# 4. Publish to a release (create the tag if absent), then upload the asset + its checksum.
tag=lean-seed-$(date -u +%Y-%m-%d)
gh release create "$tag" --title "Lean seed $tag" --notes "seed for $(git rev-parse --short HEAD)" || true
gh release upload  "$tag" "$asset" "$asset.sha256" --clobber

# 5. Bump the committed pointer so fetch-lean-seed.sh serves it, then commit + push.
{ sed -n '1,/^$/p' dregg-lean-ffi/lean-seed.pin | sed '/^$/d'; echo;
  echo "TAG=$tag";
  scripts/lean-seed-key.sh | grep -E '^(LEAN_TOOLCHAIN|MATHLIB_REV|DREGG_TREE_HASH)=';
  echo "GENERATED_UTC=$(date -u +%Y-%m-%dT%H:%M:%SZ)";
  echo "NOTE=published by hand on lassie";
} > dregg-lean-ffi/lean-seed.pin.new && mv dregg-lean-ffi/lean-seed.pin.new dregg-lean-ffi/lean-seed.pin
git add dregg-lean-ffi/lean-seed.pin
git -c commit.gpgsign=false commit -m "chore(seed): publish Lean seed $tag + bump pin"
git push
```

The **hand-back to the maintainer**: the release tag, the asset filename, and its sha256. From then
on `scripts/fetch-lean-seed.sh` links a verified node in minutes for anyone on that platform.

The compressed asset is small (~20 MB for the ~180 MB archive, ≈8.6× with `zstd -19`).

## The security posture

- The seed is **content-addressed** by a published `.sha256` sidecar; `fetch-lean-seed.sh` refuses
  to install on a checksum mismatch (corruption/tamper) and refuses an archive lacking the
  `dregg_exec_full_forest_auth` export (wrong/placeholder file).
- A seed is a *build accelerator*, not a *trust root*: the verified guarantee comes from the Lean
  proofs compiled into it, and the same source rebuilds it bit-for-bit deterministically. A paranoid
  operator can always ignore the artifact and `./scripts/bootstrap.sh` from source.
- The seed is **never** committed to the repo (`.gitignore`: `libdregg_lean.a*`) — only published as
  a release asset.

## The mathlib pin is portable (git+rev)

`metatheory/lakefile.toml` pins mathlib as a **`git`+`rev` dependency** at the exact revision
matching Lean `v4.30.0` (`1c2b90b13009c65b090d95a83c98e248deafb6f1`). `lake` fetches it into
`metatheory/.lake/packages/mathlib` on any host — a fresh clone at **any location** resolves, with
no `/Users/…` / `/home/…` / clone-depth assumption. (This replaced a host-fragile
`path = "../../../src/mathlib4"` local require that only resolved when breadstuffs was cloned exactly
two levels under `$HOME` with mathlib as a `$HOME/src` sibling — which broke a fresh Linux
cold-bootstrap on lassie.)

**Local fast path (maintainer boxes, optional — no re-download):** if you already have a warm
mathlib checkout at the pinned rev, symlink it into the packages dir *before* the first `lake build`
so lake reuses it (its warm `.lake/build` oleans and all) instead of cloning + re-fetching:

```sh
ln -sfn /path/to/your/mathlib4 metatheory/.lake/packages/mathlib
```

`.lake/` is gitignored and per-machine, so this changes nothing committed. Plain `lake build` reads
the manifest and uses whatever is in the packages dir as-is (it does not `git fetch`/`checkout` your
symlinked checkout — only `lake update` would), so the symlinked mathlib is left untouched.
