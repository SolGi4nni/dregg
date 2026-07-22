#!/bin/sh
set -eu

here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
: "${DREGG_HOLDIR:?set DREGG_HOLDIR to the HOL4 checkout}"
: "${DREGG_CAKEMLDIR:?set DREGG_CAKEMLDIR to the CakeML checkout}"
hol_dir=$DREGG_HOLDIR
cake_dir=$DREGG_CAKEMLDIR

mkdir -p "$here/build/fixtures"

(
  cd "$here/hol4"
  DREGG_CAKEMLDIR="$cake_dir" \
    "$hol_dir/bin/Holmake" --holdir "$hol_dir" \
      DirectLogicWitnessAuditTheory.uo
)

cc -O2 \
  "$here/hol4/direct_logic_witness_checker_arm8.S" \
  "$cake_dir/basis/basis_ffi.c" \
  -lm \
  -o "$here/build/direct_logic_witness_checker"

(
  cd "$here"
  poly --script test_witness_checker.sml
  poly --script emit_native_fixtures.sml
  ./test_native.sh
)
