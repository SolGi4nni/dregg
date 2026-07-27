#!/bin/sh
# Build libhealthserve.a — the cake--pancake-compiled x64 /health responder
# (health.S) plus its re-entrant in-process driver (health_ffi.c), archived as a
# runtime-free static library the dataplane links for the DRORB_HEALTH_NATIVE demo.
#
# health.S carries its own CakeML heap/GC and references only the four symbols
# health_ffi.c provides (ffiload_vec / ffireport_vec / cml_exit / cml_clear), so
# the archive needs neither the stock basis_ffi.c nor the Lean runtime.
#
# When the `cake` compiler is on PATH (or $CAKE), health.S is regenerated from
# health.pnk (itself generated from health_golden.bin); otherwise the committed
# health.S (cake --pancake output) is used as-is.
set -e
DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$DIR"

CAKE="${CAKE:-cake}"
if command -v "$CAKE" >/dev/null 2>&1; then
  echo "regenerating health.pnk + health.S with $CAKE"
  python3 gen_health.py health_golden.bin health.pnk
  "$CAKE" --pancake < health.pnk > health.S
else
  echo "cake not found — using committed health.S"
fi

# --noexecstack: the emitted machine code does not run from the stack (no EVAL
# code buffer), so mark the object non-exec-stack and keep the linked binary clean.
cc -O2 -Wa,--noexecstack -c health.S     -o health.o
cc -O2 -Wa,--noexecstack -c health_ffi.c -o health_ffi.o
rm -f libhealthserve.a
ar crs libhealthserve.a health.o health_ffi.o
echo "built $DIR/libhealthserve.a"
