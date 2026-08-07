#!/usr/bin/env bash
# THE wasm32 FLAG PAIR — ONE definition, sourced by every wasm32 build in this repo.
#
# WHY THIS FILE EXISTS
# --------------------
# `scripts/build-descent-wasm.sh` was created because THREE build paths carried their own
# copy of these flags and disagreed. It centralized the `wasm/pkg` build and its header
# says the flags "travel together here so no caller can separate them again."
#
# There was a FOURTH, and it had already separated them: `extension/build.sh` ran a bare
# `cargo build --target wasm32-unknown-unknown --release` with NO `RUSTFLAGS` at all. It
# picked `getrandom_backend` up from `.cargo/config.toml` (and only while the CWD happened
# to sit inside the repo) and it never had the stack size. So the extension's shipped blob
# was linked with wasm's 1 MiB default stack — the exact configuration the descent build's
# header calls out as overflowing.
#
# A script cannot be "the one build" for a bundle it does not build. So the INVARIANT moved
# down here, to a thing both builds READ, and the two builds above it differ only in the
# wasm-bindgen target they need (`--target web` for the site, `--target no-modules` for the
# MV3 service worker, which loads its glue with `importScripts`).
#
# THE FLAG PAIR — both, or neither works
#   -C link-arg=-zstack-size=33554432   32 MiB of linear-memory stack. The recursion
#                                       verifier overflows wasm's 1 MiB default.
#   --cfg getrandom_backend="wasm_js"   getrandom 0.3/0.4 refuse to compile for wasm32
#                                       without a backend selection.
#
# `.cargo/config.toml` sets the second under `[target.wasm32-unknown-unknown] rustflags`,
# and cargo does NOT merge that with the `RUSTFLAGS` environment variable — env WINS
# OUTRIGHT and the config flags are dropped entirely. So a build path that exports
# `RUSTFLAGS` for the stack size alone has silently deleted the getrandom selection, and a
# build path that exports nothing has silently deleted the stack size. Both are here.
#
# A SECOND, QUIETER PAYOFF: two builds that pass cargo the SAME `RUSTFLAGS` share one set
# of compiled artifacts in `wasm/target`. Before this file the extension's flagless build
# had a different fingerprint from `wasm-pack`'s, so building both meant compiling the
# wasm32 graph TWICE. Now the second build is wasm-bindgen + wasm-opt.
#
# USAGE
#   source scripts/wasm-build-flags.sh     # defines DREGG_WASM_RUSTFLAGS
#   bash   scripts/wasm-build-flags.sh     # prints it (for a workflow `run:` line)

DREGG_WASM_RUSTFLAGS='--cfg getrandom_backend="wasm_js" -C link-arg=-zstack-size=33554432'

# Executed rather than sourced: print, so a caller in another language can read one value
# out of ONE place instead of transcribing it into a fifth.
if [ "${BASH_SOURCE[0]}" = "${0}" ]; then
  printf '%s\n' "$DREGG_WASM_RUSTFLAGS"
fi
