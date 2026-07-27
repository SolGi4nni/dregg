#!/usr/bin/env bash
# Compile the untrusted UDP-client seam the `wg-live` exe links against:
#   ffi/wg_udp.c -> ffi/wg_udp.o  (send a datagram, wait bounded for one reply)
# TOML lakefiles cannot compile a C source directly, so we precompile here and
# reference the object from moreLinkArgs in lakefile.toml. Re-run whenever the C
# source changes.
#
# Uses the system C compiler with the Lean toolchain's include path so the object
# matches the runtime ABI (<lean/lean.h>) while still finding the macOS SDK system
# headers.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
inc="$(lean --print-prefix)/include"
cc -c -O2 -fPIC -I "$inc" -o "$here/wg_udp.o" "$here/wg_udp.c"
echo "built $here/wg_udp.o"
