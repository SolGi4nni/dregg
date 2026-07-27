#!/usr/bin/env bash
# The `dregg-cell/test-stubs` feature arms the ACCEPT path of `StubVerifier`, which
# otherwise fails closed on every proof. It has escaped into a production binary once
# already: `tests/Cargo.toml` had the entry under `[dependencies]` and `dregg-tests` is
# in `default-members`, so a root `cargo build --release` armed the stub accept path
# inside `dregg-node`.
#
# `cell/Cargo.toml` documents the enforcement and its own history in the same breath:
# "a comment is not an enforcement mechanism, and this one was previously FALSE".
# The enforcement is real — a `compile_error!` plus three independent resolve probes —
# but it lived only in a test crate nobody runs by hand, so the cheap gate table said
# nothing about the one feature flip that can turn a verifier into accept-anything.
#
# 3.4s, no Lean, no proving. There is no reason for this not to be in the cheap set.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.." || exit 2
out="$(cargo test -p dregg-tests --test test_stubs_firewall -- --test-threads=4 2>&1)"; rc=$?
n=$(printf '%s' "$out" | grep -oE 'test result: ok\. ([0-9]+) passed' | grep -oE '[0-9]+' | head -1)
if [ "$rc" -ne 0 ]; then printf '%s\n' "$out" | tail -12; echo "test-stubs firewall: FAILED"; exit 1; fi
# A zero-match run is this repo's signature failure. Assert the floor.
if [ -z "${n:-}" ] || [ "$n" -lt 2 ]; then
  echo "test-stubs firewall: ran ${n:-0} tests, expected >= 2 — the probe selected nothing"; exit 1
fi
echo "test-stubs firewall: $n probes pass — the accept path reaches no production graph"
