#!/usr/bin/env bash
# lane-lease-selftest.sh — the falsifier for scripts/lane-lease.sh.
#
# Runs the WHOLE lease state machine against a throwaway root via `--host local`, so it needs
# no build box, no network and about two seconds. `--host local` exists in lane-lease.sh for
# exactly this reason: the local and remote arms feed the IDENTICAL program text to the
# identical `bash -s`, so what this proves locally is what runs on persvati.
#
# WHY A SELFTEST AND NOT A PASTED TRANSCRIPT: every case here was hand-run once while the tool
# was written, and a guard proven once by hand is a guard nobody will ever check again. Each
# case asserts an EXIT CODE and an OUTPUT SUBSTRING, and the three that matter most are the
# ones that must go RED if the lease ever stops being a hint-with-an-expiry:
#   case 8/9   an EXPIRED lease is reapable         (a dead agent cannot wedge a lane)
#   case 11    a TORN lease fails closed but ages out
#   case 12    an ABSURD expires= is clamped to mtime + LANE_LEASE_MAX_AGE
#              (delete the ceiling in lane-lease.sh and case 12's second half goes red:
#               `expires=99999999999` reads held forever, which is the wedge)
#   case 13    the SIDECAR alone still holds the lane, because `rsync --delete` reaches the
#              contract path and cannot reach the sidecar (MEASURED, see lane-lease.sh)
#
#   scripts/lane-lease-selftest.sh
FAILS=0
LL="$(cd "$(dirname "$0")" && pwd)/lane-lease.sh"
R="$(mktemp -d "${TMPDIR:-/tmp}/lane-lease-selftest.XXXXXX")"
trap 'rm -rf "$R"' EXIT
mkdir -p "$R/crewbraid/target/debug/deps" "$R/native-anchor"
ll() { "$LL" "$@" --host local --root "$R"; }
ck() { # ck <label> <expected-exit> <actual-exit> [<grep-pattern> <text>]
  local label="$1" want="$2" got="$3" pat="${4:-}" txt="${5:-}"
  if [ "$want" != "$got" ]; then echo "FAIL $label: exit want=$want got=$got"; FAILS=$((FAILS+1)); return; fi
  if [ -n "$pat" ] && ! printf '%s' "$txt" | grep -qE "$pat"; then
    echo "FAIL $label: output lacks /$pat/"; printf '  got: %s\n' "$txt"; FAILS=$((FAILS+1)); return
  fi
  echo "PASS $label"
}

echo "── 1. show on an unleased lane"
o=$(ll show --lane crewbraid 2>&1); e=$?
ck "absent → exit 5" 5 $e 'state=absent' "$o"

echo "── 2. acquire, and the line matches the CONTRACT format byte for byte"
o=$(ll acquire --lane crewbraid --owner agent:lease 2>&1); e=$?
ck "acquire → exit 0" 0 $e 'state=held.*owner=agent:lease' "$o"
CF="$R/crewbraid/.pbuild-lease"; SF="$R/.leases/crewbraid.lease"
for f in "$CF" "$SF"; do
  if [ -f "$f" ]; then echo "PASS   exists: ${f#$R/}"; else echo "FAIL   missing: $f"; FAILS=$((FAILS+1)); fi
done
line=$(cat "$CF")
if printf '%s\n' "$line" | grep -qxE 'owner=[^ ]+ pid=[0-9]+ host=[^ ]+ expires=[0-9]+'; then
  echo "PASS   format exact: $line"
else echo "FAIL   format: $line"; FAILS=$((FAILS+1)); fi
if [ "$(wc -l < "$CF")" -eq 1 ]; then echo "PASS   exactly one line"; else echo "FAIL   not one line"; FAILS=$((FAILS+1)); fi
if [ "$line" = "$(cat "$SF")" ]; then echo "PASS   sidecar identical"; else echo "FAIL   sidecar differs"; FAILS=$((FAILS+1)); fi

echo "── 3. show reports held with remaining seconds"
o=$(ll show --lane crewbraid 2>&1); e=$?
ck "held → exit 0" 0 $e 'state=held .*remaining=3[0-9]{2,3}' "$o"

echo "── 4. a DIFFERENT owner cannot acquire it"
o=$(ll acquire --lane crewbraid --owner agent:intruder 2>&1); e=$?
ck "foreign acquire → REFUSED 3" 3 $e 'REFUSED.*held by .agent:lease' "$o"
if grep -q 'owner=agent:lease' "$CF"; then echo "PASS   owner unchanged"; else echo "FAIL   owner was overwritten"; FAILS=$((FAILS+1)); fi

echo "── 5. --force can take it (a hint, not a lock)"
o=$(ll acquire --lane crewbraid --owner agent:intruder --force 2>&1); e=$?
ck "forced acquire → 0" 0 $e 'owner=agent:intruder' "$o"
ll acquire --lane crewbraid --owner agent:lease --force >/dev/null 2>&1

echo "── 6. refresh NEVER refuses, and does not steal the owner"
before=$(sed -n 's/.*expires=//p' "$CF")
sleep 1
o=$(ll refresh --lane crewbraid --owner agent:pbuild 2>&1); e=$?
ck "foreign refresh → 0" 0 $e 'extending .agent:lease' "$o"
after=$(sed -n 's/.*expires=//p' "$CF")
if [ "$after" -gt "$before" ]; then echo "PASS   expiry advanced $before → $after"; else echo "FAIL   expiry did not advance"; FAILS=$((FAILS+1)); fi
if grep -q 'owner=agent:lease' "$CF"; then echo "PASS   owner preserved"; else echo "FAIL   refresh stole the owner"; FAILS=$((FAILS+1)); fi

echo "── 7. release refuses a lane you do not own, then works for the owner"
o=$(ll release --lane crewbraid --owner agent:intruder 2>&1); e=$?
ck "foreign release → REFUSED 3" 3 $e 'REFUSED' "$o"
o=$(ll release --lane crewbraid --owner agent:lease 2>&1); e=$?
ck "owner release → 0" 0 $e 'state=released' "$o"
if [ ! -e "$CF" ] && [ ! -e "$SF" ]; then echo "PASS   both copies gone"; else echo "FAIL   a copy survived release"; FAILS=$((FAILS+1)); fi
o=$(ll release --lane crewbraid --owner agent:lease 2>&1); e=$?
ck "release is idempotent" 0 $e 'nothing to release' "$o"

echo "── 8. an EXPIRED lease reads expired (TTL 0, and ANCHORLESS)"
# `--pid 0` is load-bearing since the lease became LIVENESS-based (de21b8e7f). A record with a live
# anchor holds past its clock BY DESIGN — that is the whole fix — so `--ttl 0` alone no longer means
# expired, and the default anchor is now $PPID (a live process) rather than $$ (a corpse by the next
# tool call). `--pid 0` is the explicit anchorless sentinel, which puts TTL back in charge and makes
# this case test what its name claims.
ll acquire --lane crewbraid --owner agent:dead --ttl 0 --pid 0 >/dev/null 2>&1
o=$(ll show --lane crewbraid 2>&1); e=$?
ck "expired → exit 4" 4 $e 'state=expired' "$o"

echo "── 9. reap-expired clears it, and says so"
o=$(ll reap-expired --lane crewbraid --dry-run 2>&1); e=$?
ck "dry-run → 0" 0 $e 'WOULD-REAP +crewbraid' "$o"
if [ -f "$CF" ]; then echo "PASS   dry-run deleted nothing"; else echo "FAIL   dry-run deleted the lease"; FAILS=$((FAILS+1)); fi
o=$(ll reap-expired 2>&1); e=$?
ck "reap all → 0" 0 $e 'REAPED +crewbraid' "$o"
ck "reap all counts it" 0 $e '^reap-expired: 1 cleared, 0 still held' "$o"
if [ ! -e "$CF" ] && [ ! -e "$SF" ]; then echo "PASS   both copies reaped"; else echo "FAIL   a copy survived the reap"; FAILS=$((FAILS+1)); fi

echo "── 10. reap-expired does NOT touch a live lease"
ll acquire --lane crewbraid --owner agent:live >/dev/null 2>&1
o=$(ll reap-expired 2>&1); e=$?
ck "live lease survives reap" 0 $e 'HELD +crewbraid +owner=agent:live' "$o"
ck "reap clears nothing" 0 $e '^reap-expired: 0 cleared, 1 still held' "$o"
if [ -f "$CF" ]; then echo "PASS   still there"; else echo "FAIL   reaped a live lease"; FAILS=$((FAILS+1)); fi

echo "── 11. a TORN line fails CLOSED (held) but still expires — cannot wedge"
printf 'owner=agent:torn pid=99 host=box expi' > "$CF"; rm -f "$SF"
o=$(ll show --lane crewbraid 2>&1); e=$?
ck "malformed → held (fail closed)" 0 $e 'state=held.*malformed=1' "$o"
touch -t 202001010000 "$CF"
o=$(ll show --lane crewbraid 2>&1); e=$?
ck "old malformed → expired" 4 $e 'state=expired.*malformed=1' "$o"
o=$(ll reap-expired --lane crewbraid 2>&1); e=$?
ck "reap clears a malformed lease" 0 $e 'REAPED.*malformed=1' "$o"

echo "── 12. an ABSURD expires= is CLAMPED to mtime+MAX_AGE — 250 years buys 24 hours"
printf 'owner=agent:forever pid=1 host=box expires=99999999999\n' > "$CF"
o=$(ll show --lane crewbraid 2>&1); e=$?
ck "absurd expiry → clamped, still held" 0 $e 'clamped=1' "$o"
rem=$(printf '%s' "$o" | sed -n 's/.*remaining=\([0-9-]*\).*/\1/p')
if [ "${rem:-0}" -le 86400 ]; then echo "PASS   remaining=$rem ≤ 86400 ceiling"; else echo "FAIL   remaining=$rem escaped the ceiling"; FAILS=$((FAILS+1)); fi
touch -t 202001010000 "$CF"
o=$(ll show --lane crewbraid 2>&1); e=$?
ck "aged out despite expires=99999999999" 4 $e 'state=expired' "$o"
rm -f "$CF" "$SF"

echo "── 13. the SIDECAR survives an rsync --delete of the contract copy"
ll acquire --lane crewbraid --owner agent:lease >/dev/null 2>&1
rm -f "$CF"                       # exactly what rsync --delete does to the lane root
o=$(ll show --lane crewbraid 2>&1); e=$?
ck "sidecar alone still holds" 0 $e 'state=held.*where=sidecar' "$o"
ll release --lane crewbraid --owner agent:lease >/dev/null 2>&1

echo "── 14. usage guards"
o=$($LL acquire --host local --root "$R" 2>&1); e=$?
ck "missing --lane → 2" 2 $e 'needs --lane' "$o"
o=$(ll acquire --lane crewbraid --owner 'two words' 2>&1); e=$?
ck "owner with a space → 2" 2 $e 'must not contain whitespace' "$o"
o=$(ll acquire --lane 'a/b' 2>&1); e=$?
ck "lane as a path → 2" 2 $e 'bare lane name' "$o"
o=$(ll frobnicate --lane crewbraid 2>&1); e=$?
ck "unknown verb → 2" 2 $e 'unknown verb' "$o"

echo
if [ "$FAILS" -eq 0 ]; then echo "ALL LEASE CASES PASS"; else echo "$FAILS ASSERTION(S) FAILED"; fi
exit "$FAILS"
