#!/usr/bin/env python3
"""Run the suite cases a crashed serve never reached, one case per fresh
serve instance, and merge the verdicts into reports/index.json.

Needed because a serve crash (e.g. the 9.4.4 stack overflow) aborts the
fuzzing run: every case after the crash shows up as connection-refused and
never gets a verdict. This driver gives each remaining case its own serve
process so one crash cannot shadow the next case's result.

Usage: resume.py PORT CASE_ID [CASE_ID ...]
"""
import json
import os
import shutil
import signal
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
BIN = os.path.join(HERE, ".ws-sut-snapshot")
# The suite writes reports/index.json as root (docker). Read the base run from
# it, but write the merged verdicts to a user-owned file alongside it.
BASE_INDEX = os.path.join(HERE, "reports", "index.json")
INDEX = os.path.join(HERE, "index.merged.json")


def port_open(port):
    out = subprocess.run(["ss", "-tln"], capture_output=True, text=True)
    return f":{port} " in out.stdout


def run_one(port, case_id):
    serve = subprocess.Popen(
        # Same reactor as ws/run.sh (WS_IO, default `auto` = what the shipped
        # binary picks) so a resumed case replays on the reactor the full run
        # scored it on. Was a hardcoded `blocking`.
        [BIN, "--bind", f"127.0.0.1:{port}", "--no-udp", "--io",
         os.environ.get("WS_IO", "auto")],
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    try:
        for _ in range(50):
            if port_open(port):
                break
            time.sleep(0.2)
        spec = {
            "outdir": "./reports-resume",
            "servers": [{"agent": "dataplane", "url": f"ws://127.0.0.1:{port}"}],
            "cases": [case_id],
            "exclude-cases": [],
            "exclude-agent-cases": {},
        }
        spec_path = os.path.join(HERE, "fuzzingclient.resume.json")
        with open(spec_path, "w") as f:
            json.dump(spec, f)
        timed_out = False
        try:
            subprocess.run(
                ["docker", "run", "--rm", "--network", "host",
                 "-v", f"{HERE}:/work", "-w", "/work",
                 "crossbario/autobahn-testsuite",
                 "wstest", "-m", "fuzzingclient", "-s",
                 "fuzzingclient.resume.json"],
                capture_output=True, text=True, timeout=600)
        except subprocess.TimeoutExpired:
            timed_out = True
        serve.poll()
        crashed = serve.returncode is not None
        if timed_out:
            return {"behavior": "NO VERDICT (case exceeded 600s — serve hung)",
                    "behaviorClose": "TIMEOUT", "remoteCloseCode": None}, crashed
        try:
            with open(os.path.join(HERE, "reports-resume", "index.json")) as f:
                got = json.load(f).get("dataplane", {})
        except FileNotFoundError:
            got = {}
        return got.get(case_id), crashed
    finally:
        try:
            serve.send_signal(signal.SIGKILL)
            serve.wait(timeout=5)
        except Exception:
            pass


def main():
    port = int(sys.argv[1])
    cases = sys.argv[2:]
    src = INDEX if os.path.exists(INDEX) else BASE_INDEX
    with open(src) as f:
        index = json.load(f)
    agent = index.setdefault("dataplane", {})
    for cid in cases:
        verdict, crashed = run_one(port, cid)
        if verdict is None:
            verdict = {"behavior": "NO VERDICT (serve crashed mid-case)",
                       "behaviorClose": "NONE", "remoteCloseCode": None}
        verdict["serveCrashed"] = crashed
        agent[cid] = verdict
        print(f"{cid:<10} behavior={verdict.get('behavior','?'):<40} "
              f"close={verdict.get('behaviorClose','?'):<18} "
              f"serve-crashed={crashed}", flush=True)
        # Persist after every case so one hang/crash never loses prior work.
        with open(INDEX, "w") as f:
            json.dump(index, f, indent=1)


if __name__ == "__main__":
    main()
