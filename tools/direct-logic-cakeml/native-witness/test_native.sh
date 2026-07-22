#!/bin/sh
set -eu

checker=${1:-build/direct_logic_witness_checker}

check_case() {
  fixture=$1
  expected=$2
  actual=$("$checker" < "$fixture")
  if [ "$actual" != "$expected" ]; then
    echo "FAIL: $fixture expected $expected, got $actual" >&2
    exit 1
  fi
}

check_case build/fixtures/semantic-000.drew reject
check_case build/fixtures/semantic-001.drew reject
check_case build/fixtures/semantic-010.drew reject
check_case build/fixtures/semantic-011.drew reject
check_case build/fixtures/semantic-100.drew accept
check_case build/fixtures/semantic-101.drew accept
check_case build/fixtures/semantic-110.drew reject
check_case build/fixtures/semantic-111.drew accept
check_case build/fixtures/reject-nonboolean.drew reject
check_case build/fixtures/reject-short-row.drew reject
check_case build/fixtures/reject-descriptor-tamper.drew reject
check_case build/fixtures/reject-trailing.drew reject
check_case build/fixtures/reject-truncated.drew reject
check_case build/fixtures/reject-version.drew reject
check_case build/fixtures/reject-live-length.drew reject

echo "native CakeML witness checker: exhaustive 8 rows + 7 hostile cases passed"
