#!/usr/bin/env bash
# check-kimchi-cellcommit.sh — the GATE for route B's GROUP-4 commitment binding.
#
# ⚑ WHY THIS EXISTS RATHER THAN A PILE OF `#guard`s
#
# `Dregg2.Circuit.Emit.KimchiCellCommit` emits 15,600 instructions, 76,489 witness values and
# 10,570 Kimchi rows — four Poseidon2-w16 permutations wired into the deployed GROUP-4 tree.
# `#guard` evaluates at ELABORATION time through `whnf`, which materialises the whole `List KRow`
# as an expression; measured on hbox 2026-07-30 that took the module past 20 GB resident, still
# climbing, and it had to be killed. The checks are therefore compiled and run here.
#
# THIS IS A GATE, NOT A REPORT: it exits nonzero when a check is red, and `EmitKimchiCellCommit`
# refuses to write an artifact unless the same `emissionChecksHold` is true — so the JSON the o1js
# transcriber consumes cannot come from an emission that fails one.
#
#   scripts/check-kimchi-cellcommit.sh                 # local
#   scripts/hbuild <lane> 'cd metatheory && lake env lean --run CheckKimchiCellCommit.lean'
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT/metatheory"

lake build Dregg2.Circuit.Emit.KimchiCellCommit
exec lake env lean --run CheckKimchiCellCommit.lean
