#!/usr/bin/env bash
# Compile ffi/glibc_isoc23_compat.o — a Linux-only link shim providing the
# glibc>=2.38 C23 symbols (__isoc23_sscanf / __isoc23_strto{l,ul,ll,ull}) that
# aws-lc (bundled in target/release/libaes_fallback.a, compiled by cargo against
# the system glibc headers) references, but which the older glibc shipped with
# the Lean toolchain — used at the final lean_exe link — does not define. They
# are ABI-identical to the classic symbols, so we alias them. No <stdio.h>/
# <stdlib.h> include here, to avoid re-triggering the same header redirect.
#
# macOS does not need this (no __isoc23_* redirect); the file is a no-op to build
# there but only the Linux exe link references the object (see osLink in
# lakefile.lean). Idempotent; re-run is cheap.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
cc -c -O2 -fPIC -o "$here/glibc_isoc23_compat.o" "$here/glibc_isoc23_compat.c"
echo "built $here/glibc_isoc23_compat.o (glibc C23 __isoc23_* alias shim)"
