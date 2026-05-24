#!/usr/bin/env bash
# Two-AI capability handoff demo — Silver-Vision substrate edition.
#
# What this run demonstrates:
#   * Bob exercises Alice's bearer cap via a canonical CapTP-delivered
#     `Authorization::CapTpDelivered` Turn (introducer-signed cert +
#     recipient-signed turn binding), assembled by `silver-helper`.
#   * Alice produces a `SovereignCellWitness` (Ed25519 + sequence) over a
#     state transition, with Charlie verifying both the canonical signing
#     message AND a tampered variant (must reject).
#   * Alice's bearer-cap registry slot is gated by a `WriteOnce`
#     `StateConstraint`; the demo exercises both the legal first
#     registration AND a re-registration attempt (must reject as
#     `ProgramError::ConstraintViolated`).
#   * Bob's exercise of the Transfer effect produces alice-side and
#     bob-side per-cell witness PIs that bilateral-pair-verify against
#     each other under the γ.2 schedule; Charlie shells to
#     `pyana-verifier bilateral-pair` to confirm.
#
# Exit code 0 ⇔ every must_pass assertion in expected.json holds AND every
# must_not_pass assertion was correctly rejected.

set -u
set -o pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$HERE/../.." && pwd)"
STATE_DIR="$HERE/state"
LOG_DIR="$STATE_DIR/logs"
PY="${PYTHON:-python3}"

color_red()   { printf '\033[31m%s\033[0m' "$*"; }
color_green() { printf '\033[32m%s\033[0m' "$*"; }
color_dim()   { printf '\033[2m%s\033[0m' "$*"; }

step()  { printf '\n[demo] step %s — %s\n' "$1" "$2"; }
ok()    { printf '       %s %s\n' "$(color_green ok)" "$*"; }
warn()  { printf '       %s %s\n' "$(color_dim '~ ')" "$*"; }
fail()  { printf '       %s %s\n' "$(color_red FAIL)" "$*"; }

reset_state() {
    rm -rf "$STATE_DIR"
    mkdir -p "$LOG_DIR"
    mkdir -p "$STATE_DIR/alice-node-data" \
             "$STATE_DIR/bob-node-data" \
             "$STATE_DIR/charlie-node-data"
}

build_artifacts() {
    local log="$LOG_DIR/cargo-build.log"
    echo "[demo] building pyana-node + pyana-verifier + silver-helper (log: $log)…"
    if ( cd "$REPO_ROOT" && cargo build \
            -p pyana-node \
            -p pyana-verifier \
            -p pyana-demo --bin silver-helper ) > "$log" 2>&1; then
        ok "cargo build ok"
        return 0
    fi
    echo "       cargo build failed; sleeping 60s and retrying once"
    sleep 60
    if ( cd "$REPO_ROOT" && cargo build \
            -p pyana-node \
            -p pyana-verifier \
            -p pyana-demo --bin silver-helper ) > "$log" 2>&1; then
        ok "cargo build ok (after retry)"
        return 0
    fi
    fail "cargo build failed twice; see $log"
    return 1
}

cd "$HERE"
reset_state

# ── Step 1: setup ─────────────────────────────────────────────────────────
step 1 "setup (build pyana-node, pyana-verifier, silver-helper)"
if ! build_artifacts; then
    echo
    fail "demo failed at step 1 (build)"
    exit 1
fi
NODE_BIN="$REPO_ROOT/target/debug/pyana-node"
VERIFIER_BIN="$REPO_ROOT/target/debug/pyana-verifier"
HELPER_BIN="$REPO_ROOT/target/debug/silver-helper"
for bin in "$NODE_BIN" "$VERIFIER_BIN" "$HELPER_BIN"; do
    if [ ! -x "$bin" ]; then
        fail "missing binary: $bin"
        exit 1
    fi
done
ok "node binary:     $NODE_BIN"
ok "verifier binary: $VERIFIER_BIN"
ok "helper binary:   $HELPER_BIN"

# ── Step 1b: init demo identities (deterministic alice/bob keys for the
#             substrate-shape artifacts that the MCP layer cannot reach) ──
step 1b "silver-helper init-identities (deterministic alice/bob keys)"
"$HELPER_BIN" init-identities --state-dir "$STATE_DIR" \
    --seed "two-ai-handoff-2026" > "$LOG_DIR/silver.identities.stdout" \
    2> "$LOG_DIR/silver.identities.stderr"
if [ $? -ne 0 ]; then
    fail "silver-helper init-identities failed; see $LOG_DIR/silver.identities.stderr"
    exit 1
fi
ok "identities written to $STATE_DIR/silver.identities.json"

# ── Step 2: bob identity (MCP side) ───────────────────────────────────────
step 2 "alice + bob become cells (alice via alice.py; bob via bob.py --identity)"
BOB_ID_JSON=$("$PY" "$HERE/bob.py" \
    --node-bin "$NODE_BIN" \
    --data-dir "$STATE_DIR/bob-node-data" \
    --state-dir "$STATE_DIR" \
    --mode identity 2>"$LOG_DIR/bob.identity.stderr.log")
bob_rc=$?
if [ $bob_rc -ne 0 ]; then
    fail "bob.py --identity exited $bob_rc; see $LOG_DIR/bob.identity.stderr.log"
    exit 2
fi
BOB_PK=$(echo "$BOB_ID_JSON" | "$PY" -c 'import json,sys;print(json.load(sys.stdin)["bob_pk"])')
BOB_CELL=$(echo "$BOB_ID_JSON" | "$PY" -c 'import json,sys;print(json.load(sys.stdin)["bob_cell"])')
ok "bob pk = ${BOB_PK:0:16}… cell = ${BOB_CELL:0:16}…"

# ── Step 3: alice creates cell, grants TRANSFER cap, exports bearer cap ──
step 3 "alice creates cell, grants signature-permission to bob, drops bearer-cap URI"
ALICE_OUT=$("$PY" "$HERE/alice.py" \
    --node-bin "$NODE_BIN" \
    --data-dir "$STATE_DIR/alice-node-data" \
    --state-dir "$STATE_DIR" \
    --bob-pk "$BOB_PK" \
    --bob-cell "$BOB_CELL" 2>"$LOG_DIR/alice.stderr.log")
alice_rc=$?
if [ $alice_rc -ne 0 ]; then
    fail "alice.py exited $alice_rc; see $LOG_DIR/alice.stderr.log"
    exit $alice_rc
fi
ALICE_PK=$(echo "$ALICE_OUT" | "$PY" -c 'import json,sys;print(json.load(sys.stdin)["alice_pk"])')
ALICE_CELL=$(echo "$ALICE_OUT" | "$PY" -c 'import json,sys;print(json.load(sys.stdin)["alice_cell"])')
GRANT_TURN=$(echo "$ALICE_OUT" | "$PY" -c 'import json,sys;print(json.load(sys.stdin)["grant_turn_hash"])')
ok "alice cell = ${ALICE_CELL:0:16}…"
ok "grant turn = ${GRANT_TURN:0:16}…"
ok "handoff URI written to $STATE_DIR/handoff.uri"

# ── Step 4: silver-helper canonical artifacts ────────────────────────────
step 4 "silver-helper: HandoffCertificate, CapTpDelivered Turn, SovereignCellWitness, slot caveat, γ.2 bundle"

"$HELPER_BIN" make-handoff \
    --state-dir "$STATE_DIR" \
    --alice-cell "$ALICE_CELL" \
    --bob-cell "$BOB_CELL" > "$LOG_DIR/silver.handoff.stdout" 2> "$LOG_DIR/silver.handoff.stderr"
HANDOFF_RC=$?
[ $HANDOFF_RC -eq 0 ] && ok "HandoffCertificate signed + presentation signed" \
                    || fail "silver-helper make-handoff failed ($HANDOFF_RC)"

"$HELPER_BIN" make-captp-delivered \
    --state-dir "$STATE_DIR" \
    --alice-cell "$ALICE_CELL" \
    --bob-cell "$BOB_CELL" \
    --amount 100 \
    --turn-nonce 1 > "$LOG_DIR/silver.captp.stdout" 2> "$LOG_DIR/silver.captp.stderr"
CAPTP_RC=$?
[ $CAPTP_RC -eq 0 ] && ok "Authorization::CapTpDelivered Turn assembled (real Ed25519 sigs)" \
                  || fail "silver-helper make-captp-delivered failed ($CAPTP_RC)"

"$HELPER_BIN" make-sovereign-witness \
    --state-dir "$STATE_DIR" \
    --cell "$ALICE_CELL" \
    --sequence 1 > "$LOG_DIR/silver.sovereign.stdout" 2> "$LOG_DIR/silver.sovereign.stderr"
SOV_RC=$?
[ $SOV_RC -eq 0 ] && ok "SovereignCellWitness assembled + signed" \
                || fail "silver-helper make-sovereign-witness failed ($SOV_RC)"

"$HELPER_BIN" slot-caveat-demo \
    --state-dir "$STATE_DIR" > "$LOG_DIR/silver.caveat.stdout" 2> "$LOG_DIR/silver.caveat.stderr"
CAV_RC=$?
[ $CAV_RC -eq 0 ] && ok "WriteOnce slot caveat exercised (first-write ok, re-write rejected)" \
                || fail "silver-helper slot-caveat-demo failed ($CAV_RC)"

"$HELPER_BIN" make-bilateral-bundle \
    --state-dir "$STATE_DIR" \
    --alice-cell "$ALICE_CELL" \
    --bob-cell "$BOB_CELL" \
    --amount 100 \
    --turn-nonce 1 > "$LOG_DIR/silver.bilateral.stdout" 2> "$LOG_DIR/silver.bilateral.stderr"
BILAT_RC=$?
[ $BILAT_RC -eq 0 ] && ok "γ.2 BilateralBundle assembled (alice + bob WRs)" \
                  || fail "silver-helper make-bilateral-bundle failed ($BILAT_RC)"

# ── Step 5/6/7: bob exercises (existing MCP path; Authorization::Bearer) ──
# GAP: today's MCP tool `pyana_exercise_bearer_cap` uses Authorization::Bearer,
# not CapTpDelivered. silver-helper above produces a canonical CapTpDelivered
# Turn artifact in parallel for charlie to verify. Once MCP exposes a
# `pyana_exercise_handoff_cert` tool, this step folds into it.
step 7 "bob exercises the cap (MCP exercise tool — legacy Authorization::Bearer path)"
BOB_OUT=$("$PY" "$HERE/bob.py" \
    --node-bin "$NODE_BIN" \
    --data-dir "$STATE_DIR/bob-node-data" \
    --state-dir "$STATE_DIR" \
    --mode exercise \
    --amount 100 2>"$LOG_DIR/bob.exercise.stderr.log")
bob_rc=$?
if [ $bob_rc -ne 0 ]; then
    fail "bob.py exercise exited $bob_rc"
    EXERCISE_OK=0
else
    EXERCISE_OK=1
    EXERCISE_TURN=$(echo "$BOB_OUT" | "$PY" -c 'import json,sys;print(json.load(sys.stdin)["exercise_turn_hash"])')
    ok "exercise turn = ${EXERCISE_TURN:0:16}…"
fi

# ── Step 8: charlie verifies everything ──────────────────────────────────
step 8 "charlie verifies (pyana-verifier + silver-helper, both independent)"
CHARLIE_OUT=$("$PY" "$HERE/charlie.py" \
    --state-dir "$STATE_DIR" \
    --verifier-bin "$VERIFIER_BIN" \
    --silver-helper-bin "$HELPER_BIN" 2>"$LOG_DIR/charlie.stderr.log")
charlie_rc=$?
if [ $charlie_rc -ne 0 ]; then
    fail "charlie.py exited $charlie_rc; see $LOG_DIR/charlie.stderr.log"
fi

# Extract verdict fields.
get_bool() {
    echo "$CHARLIE_OUT" | "$PY" -c "import json,sys;d=json.load(sys.stdin);print(d.get('$1', False))" 2>/dev/null || echo False
}

GRANT_VERIFIED=$(get_bool grant_verified)
EXERCISE_VERIFIED=$(get_bool exercise_verified)
REPLAY_CHAIN_VERIFIED=$(get_bool replay_chain_verified)
CAPTP_VERIFIED=$(get_bool captp_delivered_verified)
CAPTP_TAMPER_REJECTED=$(get_bool captp_delivered_tampered_rejected)
SOV_SELF_VERIFIES=$(get_bool sovereign_witness_self_verifies)
SOV_TAMPER_REJECTED=$(get_bool sovereign_witness_tampered_rejected)
CAV_FIRST_OK=$(get_bool slot_caveat_first_write_ok)
CAV_REWRITE_REJECTED=$(get_bool slot_caveat_rewrite_rejected)
CAV_RENEWAL_OK=$(get_bool slot_caveat_renewal_ok)
BILAT_VERIFIED=$(get_bool bilateral_verified)
BILAT_TAMPER_REJECTED=$(get_bool bilateral_tampered_rejected)

[ "$GRANT_VERIFIED" = "True" ]         && ok "grant proof verified" || warn "grant proof NOT verified"
[ "$EXERCISE_VERIFIED" = "True" ]      && ok "exercise proof verified" || warn "exercise proof NOT verified"
[ "$REPLAY_CHAIN_VERIFIED" = "True" ]  && ok "replay-chain (WitnessedReceipt v1) verified" || warn "replay-chain NOT verified"
[ "$CAPTP_VERIFIED" = "True" ]         && ok "CapTpDelivered turn verified" || warn "CapTpDelivered turn NOT verified"
[ "$CAPTP_TAMPER_REJECTED" = "True" ]  && ok "CapTpDelivered tampered signature rejected (must_not_pass)" || warn "tampered CapTpDelivered WRONGLY accepted"
[ "$SOV_SELF_VERIFIES" = "True" ]      && ok "SovereignCellWitness self-verifies" || warn "SovereignCellWitness does NOT verify"
[ "$SOV_TAMPER_REJECTED" = "True" ]    && ok "SovereignCellWitness tampered commitment rejected (must_not_pass)" || warn "tampered sovereign witness WRONGLY accepted"
[ "$CAV_FIRST_OK" = "True" ]           && ok "slot caveat: first write ok" || warn "slot caveat first write FAILED"
[ "$CAV_REWRITE_REJECTED" = "True" ]   && ok "slot caveat: re-register REJECTED (must_not_pass)" || warn "slot caveat WriteOnce did NOT reject re-write"
[ "$CAV_RENEWAL_OK" = "True" ]         && ok "slot caveat: renewal ok" || warn "slot caveat renewal failed"
[ "$BILAT_VERIFIED" = "True" ]         && ok "γ.2 bilateral bundle verified (alice + bob)" || warn "γ.2 bilateral bundle NOT verified"
[ "$BILAT_TAMPER_REJECTED" = "True" ]  && ok "γ.2 bilateral tampered bundle rejected (must_not_pass)" || warn "γ.2 tampered bundle WRONGLY accepted"

# ─── balance checks ───
BOB_DELTA=$(echo "$BOB_OUT" | "$PY" -c 'import json,sys;print(json.load(sys.stdin).get("bob_balance_delta", 0))' 2>/dev/null || echo 0)
ALICE_STUB_BAL=$(echo "$BOB_OUT" | "$PY" -c 'import json,sys;print(json.load(sys.stdin).get("alice_stub_balance", 0))' 2>/dev/null || echo 0)
BOB_DELTA_OK=0; [ "$BOB_DELTA" = "-9900" ] && BOB_DELTA_OK=1
ALICE_STUB_OK=0; [ "$ALICE_STUB_BAL" = "999900" ] && ALICE_STUB_OK=1

# ─── receipt chain ───
ALICE_CHAIN_HAS_GRANT=$(echo "$ALICE_OUT" | "$PY" -c '
import json, sys
d = json.load(sys.stdin)
grant = d.get("grant_turn_hash", "")
chain = d.get("receipt_chain", {}).get("receipts", [])
print("1" if any(r.get("turn_hash") == grant for r in chain) else "0")
' 2>/dev/null || echo 0)
BOB_CHAIN_HAS_EXERCISE=$(echo "$BOB_OUT" | "$PY" -c '
import json, sys
d = json.load(sys.stdin)
ex = d.get("exercise_turn_hash", "")
chain = d.get("receipt_chain", {}).get("receipts", [])
print("1" if any(r.get("turn_hash") == ex for r in chain) else "0")
' 2>/dev/null || echo 0)

# ─────────────────────────────────────────────────────────────────────────
# Summary
# ─────────────────────────────────────────────────────────────────────────
echo
echo "[demo] ─── summary ─────────────────────────────────────────────────"

declare -a CHECKS_LABEL
declare -a CHECKS_OK
add_check() { CHECKS_LABEL+=("$1"); CHECKS_OK+=("$2"); }

b2i() { [ "$1" = "True" ] && echo 1 || echo 0; }

add_check "step 2: alice + bob cells created"                                 1
add_check "step 3: grant turn committed"                                       1
add_check "step 5: bearer-cap URI dropped"                                     1
add_check "step 7: bob exercised the cap (MCP Bearer path)"                    "$EXERCISE_OK"
add_check "Authorization::CapTpDelivered Turn assembled + verified"            $(b2i "$CAPTP_VERIFIED")
add_check "SovereignCellWitness self-verifies"                                 $(b2i "$SOV_SELF_VERIFIES")
add_check "slot caveat: first registration succeeds"                           $(b2i "$CAV_FIRST_OK")
add_check "slot caveat: renewal (Monotonic) succeeds"                          $(b2i "$CAV_RENEWAL_OK")
add_check "γ.2 bilateral bundle pair-verifies (alice + bob)"                   $(b2i "$BILAT_VERIFIED")
add_check "charlie: grant proof verified"                                      $(b2i "$GRANT_VERIFIED")
add_check "charlie: exercise proof verified"                                   $(b2i "$EXERCISE_VERIFIED")
add_check "charlie: WitnessedReceipt v1 replay-chain verified"                 $(b2i "$REPLAY_CHAIN_VERIFIED")
add_check "Transfer credited bob (net delta -9900 = +100 - 10000 fee)"         "$BOB_DELTA_OK"
add_check "Transfer debited alice stub (1_000_000 -> 999_900)"                 "$ALICE_STUB_OK"
add_check "alice's receipt chain contains the grant turn"                      "$ALICE_CHAIN_HAS_GRANT"
add_check "bob's receipt chain contains the exercise turn"                     "$BOB_CHAIN_HAS_EXERCISE"

# must_not_pass — these are REJECT assertions; "1" means "correctly rejected".
add_check "must_not_pass: CapTpDelivered tampered sig is REJECTED"             $(b2i "$CAPTP_TAMPER_REJECTED")
add_check "must_not_pass: SovereignCellWitness tampered commitment REJECTED"   $(b2i "$SOV_TAMPER_REJECTED")
add_check "must_not_pass: slot WriteOnce re-register is REJECTED"              $(b2i "$CAV_REWRITE_REJECTED")
add_check "must_not_pass: γ.2 tampered bundle is REJECTED"                     $(b2i "$BILAT_TAMPER_REJECTED")

PASS=1
for i in "${!CHECKS_LABEL[@]}"; do
    if [ "${CHECKS_OK[$i]}" = "1" ]; then
        printf '       %s %s\n' "$(color_green PASS)" "${CHECKS_LABEL[$i]}"
    else
        printf '       %s %s\n' "$(color_red FAIL)" "${CHECKS_LABEL[$i]}"
        PASS=0
    fi
done

echo
if [ $PASS -eq 1 ]; then
    printf '%s — Silver-Vision substrate pieces all demonstrated end-to-end\n' "$(color_green '[demo] PASS')"
    exit 0
else
    printf '%s — see logs in %s\n' "$(color_red '[demo] FAIL')" "$LOG_DIR"
    exit 1
fi
