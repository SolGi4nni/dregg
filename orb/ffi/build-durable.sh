#!/usr/bin/env bash
# Compile the durable-commit syscall seam:
#   ffi/durable.c -> ffi/durable.o   (fsync a file, fsync a directory)
# Lake cannot compile a C source from a lakefile target, so — exactly as
# ffi/build-control-net.sh does — we precompile here and reference the object
# from moreLinkArgs in lakefile.lean. Re-run whenever the C source changes.
#
# The include path MUST come from the toolchain the repo pins (lean-toolchain),
# not from whatever `lean` is first on PATH: elan resolves the toolchain from the
# CURRENT DIRECTORY, so running this script from $HOME picked up the default
# toolchain, whose <lean/config.h> has a different allocator selection, and the
# resulting object failed to link with `undefined symbol: lean_alloc_small`.
# Hence the cd to the repo root before asking for the prefix.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/.." && pwd)"
inc="$(cd "$root" && lean --print-prefix)/include"
echo "using toolchain include: $inc"
cc -c -O2 -fPIC -I "$inc" -o "$here/durable.o" "$here/durable.c"
echo "built $here/durable.o"
