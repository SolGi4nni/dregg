#!/usr/bin/env python3
"""Collapse an Autobahn fuzzingclient reports/index.json into a per-case-group
pass/fail table. Groups are the suite's top-level sections (1.* framing,
2.* pings/pongs, 3.* reserved bits, 4.* opcodes, 5.* fragmentation,
6.* UTF-8, 7.* close handling, 9.* limits/performance, 10.* misc)."""
import json
import sys
from collections import defaultdict

GROUP_NAMES = {
    "1": "framing (text/binary echo)",
    "2": "pings/pongs",
    "3": "reserved bits",
    "4": "opcodes",
    "5": "fragmentation",
    "6": "UTF-8 handling",
    "7": "close handling",
    "9": "limits/performance",
    "10": "misc (auto-fragmentation)",
    "12": "compression (permessage-deflate)",
    "13": "compression (parameters)",
}

# Autobahn behavior verdicts. NON-STRICT counts as pass; INFORMATIONAL is
# reported separately (no verdict).
PASS = {"OK", "NON-STRICT"}
INFO = {"INFORMATIONAL", "UNIMPLEMENTED"}


def main(path):
    with open(path) as f:
        index = json.load(f)
    agents = list(index.keys())
    if not agents:
        print("no agents in index.json")
        return 1
    agent = agents[0]
    cases = index[agent]

    groups = defaultdict(lambda: {"pass": 0, "fail": 0, "info": 0,
                                  "fail_cases": []})
    total_pass = total_fail = total_info = 0
    for case_id, r in sorted(cases.items(),
                             key=lambda kv: [int(x) for x in kv[0].split(".")]):
        top = case_id.split(".")[0]
        b = r.get("behavior", "?")
        bc = r.get("behaviorClose", "?")
        # A case passes only if both the behavior and the close behavior pass.
        if b in INFO:
            groups[top]["info"] += 1
            total_info += 1
        elif b in PASS and bc in (PASS | INFO):
            groups[top]["pass"] += 1
            total_pass += 1
        else:
            groups[top]["fail"] += 1
            groups[top]["fail_cases"].append((case_id, b, bc))
            total_fail += 1

    print(f"agent: {agent}   cases: {len(cases)}   "
          f"pass: {total_pass}  fail: {total_fail}  info: {total_info}\n")
    print(f"{'group':<6} {'name':<34} {'pass':>5} {'fail':>5} {'info':>5}")
    for top in sorted(groups, key=int):
        g = groups[top]
        name = GROUP_NAMES.get(top, "?")
        print(f"{top + '.*':<6} {name:<34} {g['pass']:>5} {g['fail']:>5} "
              f"{g['info']:>5}")
    print()
    for top in sorted(groups, key=int):
        fc = groups[top]["fail_cases"]
        if fc:
            print(f"-- {top}.* failures ({len(fc)}):")
            for cid, b, bc in fc:
                print(f"   {cid:<10} behavior={b:<12} close={bc}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else "reports/index.json"))
