#!/usr/bin/env bash
# P2.F — CI grep guard: forbid `Authorization::Unchecked` outside of
# test code and a small, explicitly-listed escape-hatch surface.
#
# Background: the DSL audit (P0 #1) found that production framework code
# was constructing actions with `Authorization::Unchecked`, effectively
# making them unauthenticated. P2.A introduced a typestate ActionBuilder
# whose only path to that variant is the loudly-named
# `new_unchecked_for_tests` constructor. This script keeps the audit
# honest by tripwiring any new production-code reintroduction of the
# literal.
#
# Pass/fail policy:
#   - Lines in `.rs` files anywhere under a `tests/` directory: ALLOWED
#   - Lines in `*tests*.rs` files (e.g. `tests.rs`, `proptest_*.rs`,
#     `*_test.rs`): ALLOWED
#   - Comment lines (`//`, `///`, `//!`): ALLOWED (talking about it is fine)
#   - Match arms (`Authorization::Unchecked =>`): ALLOWED (handler code
#     must dispatch on the variant somewhere)
#   - The enum variant definition itself: ALLOWED
#   - Lines guarded by `!matches!` / `debug_assert!` / `assert!` /
#     `refusing` / `Refusing` (defensive checks): ALLOWED
#   - Files on the ALLOWLIST below: ALLOWED with reason
#   - Everything else: FAIL.
#
# Run from the repo root: `scripts/no-unchecked-auth.sh`

set -euo pipefail
shopt -s extglob

# Files that legitimately reference the literal in production code.
# Each entry needs a one-line reason. Touching this list should require
# a code review.
ALLOWLIST_FILE_PATTERNS=(
    # The typestate's escape hatch -- the *only* documented path to
    # Unchecked authorization, named loudly enough that nobody can
    # accidentally invoke it in production.
    "turn/src/builder.rs"
    # The Effect-VM / executor path that *consumes* the variant when
    # routing CapTP wire messages. The cryptographic legitimacy is
    # established off-band (swiss-number / handoff). Tracked as a P3
    # follow-up: replace with a typed `BridgedFromWire` authorization.
    "wire/src/captp_routing.rs"
    # The action.rs enum definition itself plus its match-arm handlers
    # in the executor / forest -- variant must be referenced somewhere.
    "turn/src/action.rs"
    "turn/src/executor.rs"
    "turn/src/eventual.rs"
    "turn/src/pending.rs"
    # The four-layer lowering uses `!matches!` defensive guards against
    # the variant slipping through SealedTurn.
    "intent/src/lowering.rs"
    # `coord/src/tests.rs` is a test fixture file living in src/.
    "coord/src/tests.rs"
    # protocol-tests is an entire crate of test scaffolding.
    "protocol-tests/src"
    # `dregg-tests` (the `tests/` crate, lib path src/main.rs) is, like
    # protocol-tests, wall-to-wall integration/threat scaffolding
    # (adversarial_*, *_threats, *_variants, …). Its paths begin with `tests/`
    # with no leading slash, so the `*/tests/*` skip above does not reach them;
    # allowlist the crate's src/ explicitly (subsumes the earlier per-file
    # every_variant_roundtrip.rs grandfather below).
    "tests/src"
    # cross-federation test scaffolding in teasting/.
    "teasting/tests"
    # The legacy LegacyActionBuilder still emits Unchecked; the
    # migration off it is tracked separately. Lives in builder.rs which
    # is already allowlisted above.

    # ─── Migration baseline (P2.F) ────────────────────────────────────
    # The following files contain pre-existing `Authorization::Unchecked`
    # usages from before the DSL hardening landed. The full migration
    # off the legacy `&mut`-chain builder is a deliberate follow-up
    # commit AFTER the P2 / P3 / P4 parallel slate lands. These files
    # are grandfathered for now; the guard's job today is to prevent
    # *net-new* production sites, not to ratchet existing ones in a
    # single commit.
    "apps/gallery/src/artwork.rs"
    "apps/gallery/src/settlement.rs"
    "apps/bounty-board/src/payment.rs"
    "demo-agent/examples"
    "intent/src/fulfillment.rs"
    "node/src/api.rs"
    "node/src/mcp.rs"
    "sdk/src/committed_turn.rs"
    "sdk/src/runtime.rs"
    "sdk/src/cipherclerk.rs"
    "tests/src/every_variant_roundtrip.rs"
    "app-framework/src/authorizer.rs"
    # `app-framework/src/escrow.rs` is NOT allowlisted: P0f migrated it to
    # the Authorizer-injected constructor, leaving only comments that
    # reference the literal (which the comment skip handles).
    # SDK-consensus demo: a CLI scaffold whose entire purpose is end-to-end
    # plumbing demos against the in-memory engine. Tracked as a follow-up
    # migration alongside the other demo-agent examples.
    "demo/sdk-consensus/src/main.rs"

    # ─── Bridging surfaces (off-band authorization established by the carrier) ──
    # The coord diff/leg builders construct the *settlement-half* transfer of an
    # already-agreed bilateral swap. Both legs were authorized when the parties
    # signed the coordination envelope; the synthesized inner transfer carries
    # `Unchecked` because its authority is the enclosing signed agreement, not a
    # second per-action signature. Same shape (and same P3 follow-up — a typed
    # `BridgedFromAgreement` authorization) as the allowlisted `captp_routing.rs`.
    "coord/src/coord_diff.rs"
    "coord/src/entangled_diff.rs"
    "coord/src/private_leg.rs"
    # The Firmament n=1 surface: a window-manager / distributed twin drives surface
    # verbs (present/embed/grant-input/revoke, delegate-grant) through the executor.
    # Authorization is the seL4 capability the caller already holds (the local
    # cap IS the proof); the bridged `Action` carries `Unchecked` because re-signing
    # a local seL4-cap-gated verb would be redundant. The executor still enforces
    # the receipt chain + nonce. Bridging surface, same rationale as captp_routing.
    "sel4/dregg-firmament/src"
    # The starbridge-v2 desktop compositor world/edit surface: the same
    # local-cap-is-the-proof bridge, one rung up (the cockpit issues window turns
    # the local user already owns). Bridging surface.
    "starbridge-v2/src"
    # The SDK's raw/remote action plumbing builds the unsigned action skeleton that
    # the caller's `sign()` then authorizes; `Unchecked` is the pre-signature
    # placeholder on the wire-construction half, never a committed turn (the SDK's
    # `sign()` refuses to emit an `Unchecked` committed action).
    "sdk/src/raw.rs"
    "sdk/src/remote.rs"
    # The observability tool ENUMERATES every Authorization variant (including
    # Unchecked) to emit a telemetry event per variant — it references the variant
    # as data for display, it does not construct an unauthenticated action.
    "observability/src/main.rs"
    # The two-ai-handoff demo helper (a loose .rs alongside the demo's python
    # drivers) builds the introduce/transfer actions for the bilateral-handoff
    # walkthrough; `Unchecked` is deliberate — bilateral verification operates on
    # the call-forest + nonce schedule, not the per-action auth path (see the
    # in-file comment). Demo scaffolding, same class as demo-agent/examples.
    "demo/two-ai-handoff/silver_helper.rs"
    # The userspace verifier DETECTS and REPORTS Unchecked (error-message string
    # literals + `matches!` membership tests in the boundary checker) — the polar
    # opposite of constructing it. It is the tool that fails a forest carrying the
    # variant outside genesis.
    "dregg-userspace-verify/src"
)

ROOT="${1:-$(git rev-parse --show-toplevel 2>/dev/null || pwd)}"

cd "$ROOT"

# Substring we are scanning for, assembled at runtime so this script
# itself does not contain the literal token.
NEEDLE=$(printf 'Authorization%s%s' '::' 'Unchecked')

offenders=()

# shellcheck disable=SC2207
files=($(git ls-files '*.rs' 2>/dev/null || find . -name '*.rs' -type f))

for file in "${files[@]}"; do
    # Skip test-shaped paths.
    case "$file" in
        */tests/*) continue ;;
        */test/*) continue ;;
    esac
    base=$(basename "$file")
    case "$base" in
        tests.rs|test.rs|*_test.rs|*_tests.rs|proptest_*.rs|*_proptest.rs) continue ;;
    esac

    # Skip allowlisted files / directories.
    skip=false
    for allowed in "${ALLOWLIST_FILE_PATTERNS[@]}"; do
        case "$file" in
            "$allowed"|"$allowed"/*|*/"$allowed"|*/"$allowed"/*)
                skip=true; break ;;
        esac
    done
    $skip && continue

    # Inline `#[cfg(test)]` modules living in a `src/` file are test code by the
    # same policy as a `tests/` directory: the typestate's `new_unchecked_for_tests`
    # path and hand-built fixtures legitimately name the variant. We can't move them
    # to a `tests/` path (they exercise crate-private internals), so we skip the
    # body of a `#[cfg(test)] mod … { … }` region. Only a leading-attribute
    # `#[cfg(test)]` immediately preceding a `mod …{` opens a tracked region; an
    # inner `#[cfg(test)]` on a single item does not (it gates one fn, not a body
    # we can bound by braces alone), so those still get the per-line skips below.
    # Pre-filter the whole file to test-module line ranges ONCE with awk (fast),
    # so the hot per-line bash loop below stays cheap. `awk` tracks the brace
    # depth of a `#[cfg(test)] mod … { … }` region and prints the 1-based line
    # numbers that fall inside it; we load those into an associative set.
    #
    # A top-level `#[cfg(<…test…>)] mod NAME { … }` always closes with a `}` in
    # column 0 (rustfmt guarantees it), so we bound the region by that closing
    # `^}` rather than by counting braces (which a `{`/`}` inside a string or a
    # `format!`/`quote!` body would throw off). The cfg attribute may gate on
    # `test` directly (`#[cfg(test)]`) or compounded (`#[cfg(all(test, …))]`,
    # `#[cfg(any(test, …))]`) — a portable BSD/GNU-awk regex matches the `test`
    # cfg word without word-boundary escapes.
    declare -A in_test_mod=()
    while IFS= read -r tl; do in_test_mod[$tl]=1; done < <(
        awk '
            /^[[:space:]]*#\[cfg\([^)]*[(, ]?test[,) ]/ { pending=1; next }
            {
                if (inmod) {
                    print NR;
                    if ($0 ~ /^\}/) inmod=0;   # column-0 close ends the module
                    next;
                }
                # A top-level `mod NAME {` (column 0, no leading indent) right
                # after a pending cfg-test attribute opens the tracked region.
                if (pending && $0 ~ /^mod[[:space:]].*\{[[:space:]]*$/) {
                    inmod=1; pending=0; next;
                }
                if ($0 !~ /^[[:space:]]*$/) pending=0;
            }
        ' "$file"
    )

    lineno=0
    while IFS= read -r line; do
        lineno=$((lineno + 1))

        case "$line" in
            *"$NEEDLE"*) ;;
            *) continue ;;
        esac

        # Skip inline #[cfg(test)] module bodies (test code in a src/ file).
        [ -n "${in_test_mod[$lineno]:-}" ] && continue

        trimmed=${line##+([[:space:]])}

        # Skip comment lines.
        case "$trimmed" in
            //*|/\**) continue ;;
        esac
        # Skip match arms.
        case "$trimmed" in
            *"$NEEDLE"*"=>"*) continue ;;
        esac
        # Skip the enum variant definition (just the identifier with
        # nothing on either side beyond punctuation).
        case "$trimmed" in
            "$NEEDLE,") continue ;;
            "$NEEDLE") continue ;;
        esac
        # Skip defensive guards and dispatch/detection. A bare `matches!(…
        # Unchecked …)` is a boolean test (reject/route on the variant), never a
        # construction — same intent as the already-skipped `!matches!`.
        case "$line" in
            *"matches!"*|*"debug_assert"*|*"refusing"*|*"Refusing"*) continue ;;
        esac

        offenders+=("$file:$lineno: $line")
    done < "$file"
done

if [ ${#offenders[@]} -gt 0 ]; then
    echo "no-unchecked-auth.sh: production code references the forbidden literal."
    echo
    printf '  %s\n' "${offenders[@]}"
    echo
    echo "If the use is legitimate production scaffolding (e.g. a deliberate"
    echo "wire-layer bridging surface), add the file to ALLOWLIST_FILE_PATTERNS"
    echo "with a reason. Otherwise use a real Authorization variant."
    exit 1
fi

echo "no-unchecked-auth.sh: ok"
exit 0
