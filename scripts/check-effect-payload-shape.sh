#!/usr/bin/env bash
# check-effect-payload-shape.sh -- run the effect PAYLOAD-SHAPE gate
# (turn/tests/effect_payload_shape_gate.rs) from local-gates.sh.
#
# WHY A WRAPPER: local-gates.sh's GATES rows are `name|timeout|command`, and the
# runner treats the command's SECOND token as a script path it stat()s before
# running (a missing script is reported as a FINDING, not a skip). `cargo test
# -p dregg-turn ...` has `test` in that position, so a bare cargo row would be
# reported MISSING forever. This file is that second token.
#
# WHAT IT GATES: `verb_registry_cover_gate.rs` pins Effect variant NAMES against
# the Lean EffectTag constructor names; every EffectTag constructor is nullary,
# so it cannot see a payload at all. A missing PARAMETER is what cost ~130 red
# tests on 2026-07-26 (Effect::Transfer has no asset field while the executor
# guard at apply.rs:673 cites the asset-indexed kernel recTransferBal and
# substitutes token_id, which is the CellId derivation nonce). The three tests
# here pin payload field lists against the Lean model's own declared
# correspondence, the asset index specifically, and the receipt layer's
# asset-naming summaries against the effects that produce them.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.." || exit 2

exec cargo test -p dregg-turn --test effect_payload_shape_gate -- --test-threads=4
