#!/usr/bin/env bash
# Drive the in-process codec fuzzer across surfaces and seeds. On a fatal
# signal (rc 97) or watchdog hang (rc 98) the harness has written the culprit
# input to the per-run state file; the driver records it, resumes PAST that
# index on a fresh process, and keeps going so one crash never ends a campaign.
# Every number printed is from an actual run.
set -u
cd "$(dirname "$0")"
export PATH=$HOME/.elan/bin:$HOME/.cargo/bin:$PATH
PFX=$(lean --print-prefix); export LD_LIBRARY_PATH=$PFX/lib/lean
BIN=./codec_fuzz
CRASHLOG=crashes.txt; : > "$CRASHLOG"
SUMMARY=campaign_summary.txt; : > "$SUMMARY"

run_surface() {
  local surface=$1 count=$2; shift 2; local seeds=("$@")
  local total=0 crashes=0
  for seed in "${seeds[@]}"; do
    local start=0 guard=0
    while :; do
      local st="st_${surface}_${seed}.txt"; : > "$st"
      out=$(taskset -c 0-7 nice -n 15 "$BIN" --surface "$surface" --count "$count" --start "$start" --seed "$seed" --state "$st" 2>&1)
      rc=$?
      if [ $rc -eq 0 ]; then
        total=$((total + count - start)); break
      elif [ $rc -eq 97 ] || [ $rc -eq 98 ]; then
        crashes=$((crashes+1))
        idx=$(sed -n 's/^index=//p' "$st" | head -1)
        {
          echo "== CRASH surface=$surface seed=$seed rc=$rc =="
          cat "$st"
          echo
        } >> "$CRASHLOG"
        # resume just past the culprit index
        start=$((idx + 1))
        guard=$((guard+1))
        if [ "$guard" -gt 200 ]; then echo "surface=$surface seed=$seed: >200 crashes, stopping this seed" >> "$SUMMARY"; total=$((total+start)); break; fi
      else
        echo "surface=$surface seed=$seed: UNEXPECTED rc=$rc out=[$out]" >> "$SUMMARY"; break
      fi
    done
  done
  echo "$surface: ran ~$total cases across ${#seeds[@]} seeds, crashes=$crashes" | tee -a "$SUMMARY"
}

run_surface frame 4000000 11 22 33 44 55
run_surface ws    4000000 11 22 33 44 55
run_surface h2    1000000 11 22 33 44 55

echo "=== DONE ===" | tee -a "$SUMMARY"
echo "crashes recorded: $(grep -c '== CRASH' "$CRASHLOG")" | tee -a "$SUMMARY"
