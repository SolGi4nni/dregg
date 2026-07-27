#!/usr/bin/env bash
# env-flag-audit.sh — the ratchet for the two hand-maintained operator tables:
# `REACTOR_SCOPED_FLAGS` (crates/dataplane/src/main.rs, mirrored by
# docs/gateway/ENV-BY-REACTOR.md) and the `DRORB_SPAN` ACME guard's
# `SELECTABLE_SPANS` / `ACME_SERVING_SPANS` (main.rs, mirrored by
# docs/gateway/ACME-SPAN-AUDIT.md).
#
# A flag or a span that changes on one side and not the other goes back to being
# silently ignored — which is exactly how `DRORB_GATEWAY` was dropped by the
# production reactor for months, and how a `DRORB_SPAN` that cannot answer ACME
# HTTP-01 becomes selectable with no warning.
#
#   scripts/env-flag-audit.sh          full report (exit 1 on any finding)
#   scripts/env-flag-audit.sh --check  CI gate: quiet on success
#   scripts/env-flag-audit.sh --list   the derived tables, always exit 0
#
# Pure source analysis: no build, no running server, well under a second.
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 scripts/env-flag-audit.py "$@"
