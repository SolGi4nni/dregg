#!/usr/bin/env python3
"""Unified conformance scoreboard for the deployed serve.

Runs EVERY available conformance suite against a freshly-launched `dataplane`
serve, aggregates the per-check verdicts, and writes an honest scoreboard:
total checks, total pass, pass-rate, per-suite breakdown, and the aggregated
gap list (every FAIL across every suite = the master to-do).

Registered suites (run when present, reported PENDING when not landed yet):

  rfc-core   conformance/rfc_conformance.py       HTTP/1.1 base (RFC 7230/7231)
  rfc-ext    conformance/rfc_conformance_ext.py   HTTP/1.1 extended (RFC 7230-7233)
  rfc-full   conformance/rfc_conformance_full.py  (pending until landed)
  h2         conformance/h2/bin/h2spec            HTTP/2 (RFC 7540/7541), 146 checks
  ws         conformance/ws/                      WebSocket (pending until landed)
  diff       conformance/differential/            differential vs reference (pending)

Honesty rules baked in:
  - every number comes from an actual run in this invocation; nothing is reused
    from stale results files (results are matched by mtime > suite start);
  - a suite that cannot run is reported PENDING or ERROR, never guessed;
  - FAILs are findings: they are itemized in the gap list, not hidden. The
    destructive check (ext Z1) runs by default because this scoreboard owns a
    dedicated serve instance and relaunches it between suites.

The serve is launched on a dedicated port (default 18906, env
CONF_SCOREBOARD_PORT) so concurrent work on other ports is untouched. Only the
serve THIS script launched is ever killed (by pid, never by name). The h2 suite
runs h2spec one section at a time because several h2 frames currently abort the
serve process — the runner relaunches between sections so one crash cannot mask
the verdicts of the remaining sections (each crash is itself recorded).

Usage:
    python3 conformance/scoreboard.py                 # run everything available
    CONF_SCOREBOARD_PORT=18906 CONF_IO=blocking \
      CONF_DESTRUCTIVE=1 python3 conformance/scoreboard.py

Outputs (in conformance/): SCOREBOARD.md, results_scoreboard.json.
Exit code is always 0 — FAILs are findings, not harness errors.
"""
import json
import os
import re
import shutil
import signal
import socket
import subprocess
import sys
import time
import xml.etree.ElementTree as ET

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
BINARY = os.path.join(ROOT, "target", "release", "dataplane")
HOST = os.environ.get("CONF_HTTP_HOST", "127.0.0.1")
PORT = int(os.environ.get("CONF_SCOREBOARD_PORT", "18906"))
IO = os.environ.get("CONF_IO", "blocking")
DESTRUCTIVE = os.environ.get("CONF_DESTRUCTIVE", "1")  # scoreboard owns its serve
H2SPEC = os.path.join(HERE, "h2", "bin", "h2spec")
PYTHON = sys.executable or "python3"


# ---------------------------------------------------------------------------
# Serve lifecycle — launch a dedicated instance, kill only what we launched.
# ---------------------------------------------------------------------------
class Serve:
    def __init__(self):
        self.proc = None
        self.log = os.path.join(HERE, f"scoreboard-serve-{PORT}.log")
        self.launches = 0

    def env(self):
        e = dict(os.environ)
        hacl = e.get("HACL_DIST", os.path.expanduser("~/src/hacl-star/dist/gcc-compatible"))
        e["HACL_DIST"] = hacl
        e["LD_LIBRARY_PATH"] = hacl + ":" + e.get("LD_LIBRARY_PATH", "")
        e["DRORB_RUST_GZIP"] = "1"
        e["DRORB_EFFECT_SEAM"] = "1"
        return e

    def alive(self):
        try:
            s = socket.create_connection((HOST, PORT), timeout=2.0)
        except OSError:
            return False
        try:
            s.sendall(b"GET /health HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
            s.settimeout(2.0)
            return b"200" in (s.recv(256) or b"")
        except OSError:
            return False
        finally:
            s.close()

    def launch(self):
        self.stop()
        # The binary may be swapped by a concurrent rebuild; retry through the
        # window where it is mid-write (ETXTBSY / partial file).
        for attempt in range(10):
            try:
                logf = open(self.log, "ab")
                self.proc = subprocess.Popen(
                    [BINARY, "--bind", f"{HOST}:{PORT}", "--no-udp", "--io", IO],
                    cwd=ROOT, env=self.env(), stdout=logf, stderr=logf,
                    stdin=subprocess.DEVNULL, start_new_session=True)
            except OSError as e:
                print(f"  [serve] exec failed ({e}); retry {attempt+1}/10", file=sys.stderr)
                time.sleep(2.0)
                continue
            for _ in range(50):
                if self.alive():
                    self.launches += 1
                    return True
                if self.proc.poll() is not None:
                    break
                time.sleep(0.1)
            self.stop()
            time.sleep(1.0)
        return False

    def ensure(self):
        if self.alive():
            return True
        return self.launch()

    def stop(self):
        if self.proc is not None:
            try:
                os.killpg(self.proc.pid, signal.SIGKILL)
            except (ProcessLookupError, PermissionError, OSError):
                try:
                    self.proc.kill()
                except OSError:
                    pass
            try:
                self.proc.wait(timeout=5)
            except Exception:
                pass
            self.proc = None


# ---------------------------------------------------------------------------
# Suite adapters. Each returns a dict:
#   {id, title, status: RAN|PENDING|ERROR, pass, fail, skip, checks: [...],
#    note}
# with checks = [{id, verdict, criterion, observed}].
# ---------------------------------------------------------------------------
def parse_results_json(path, start_ts):
    """Load a suite's results file only if this run actually (re)wrote it."""
    if not os.path.exists(path) or os.path.getmtime(path) < start_ts:
        return None
    with open(path) as f:
        d = json.load(f)
    if not isinstance(d, dict) or not isinstance(d.get("checks"), list):
        return None
    return d


def run_python_suite(sid, title, script, results_file, extra_env=None):
    if not os.path.exists(script):
        return {"id": sid, "title": title, "status": "PENDING",
                "pass": 0, "fail": 0, "skip": 0, "checks": [],
                "note": f"{os.path.basename(script)} not landed yet"}
    env = dict(os.environ)
    env["CONF_HTTP_HOST"] = HOST
    env["CONF_HTTP_PORT"] = str(PORT)
    env.update(extra_env or {})
    start = time.time()
    try:
        p = subprocess.run([PYTHON, script], cwd=HERE, env=env,
                           capture_output=True, text=True, timeout=900)
    except subprocess.TimeoutExpired:
        return {"id": sid, "title": title, "status": "ERROR",
                "pass": 0, "fail": 0, "skip": 0, "checks": [],
                "note": "suite timed out (900s)"}
    d = parse_results_json(os.path.join(HERE, results_file), start)
    if d is None:
        tail = (p.stdout + p.stderr).strip().splitlines()[-3:]
        return {"id": sid, "title": title, "status": "ERROR",
                "pass": 0, "fail": 0, "skip": 0, "checks": [],
                "note": f"exit={p.returncode}, no fresh {results_file}; tail={tail}"}
    checks = []
    for c in d["checks"]:
        checks.append({
            "id": c.get("id", "?"),
            "verdict": c.get("verdict", "FAIL"),
            "criterion": f"[{c.get('rfc', '')}] {c.get('criterion', '')}".strip(),
            "observed": c.get("observed", ""),
        })
    return {"id": sid, "title": title, "status": "RAN",
            "pass": sum(1 for c in checks if c["verdict"] == "PASS"),
            "fail": sum(1 for c in checks if c["verdict"] == "FAIL"),
            "skip": sum(1 for c in checks if c["verdict"] not in ("PASS", "FAIL")),
            "checks": checks, "note": ""}


def h2spec_sections():
    """Enumerate runnable leaf sections + expected case counts via --dryrun."""
    p = subprocess.run([H2SPEC, "--dryrun"], capture_output=True, text=True, timeout=60)
    group = None
    section = None
    out = []  # (spec_arg, ncases)
    counts = {}
    for line in p.stdout.splitlines():
        if not line.strip():
            continue
        indent = len(line) - len(line.lstrip())
        s = line.strip()
        if indent == 0:
            low = s.lower()
            if low.startswith("generic"):
                group = "generic"
            elif low.startswith("hpack"):
                group = "hpack"
            else:
                group = "http2"
            continue
        m = re.match(r"^(\d+(?:\.\d+)*)\. ", s)
        if m:
            section = f"{group}/{m.group(1)}"
            continue
        if re.match(r"^\d+: ", s) and section:
            counts[section] = counts.get(section, 0) + 1
    # only sections that directly contain cases are runnable leaves we need
    for sec, n in counts.items():
        out.append((sec, n))
    return out


def parse_junit(path, section):
    checks = []
    try:
        root = ET.parse(path).getroot()
    except (ET.ParseError, OSError):
        return checks
    for tc in root.iter("testcase"):
        pkg = tc.get("package") or section
        name = tc.get("classname") or tc.get("name") or "?"
        fail = tc.find("failure")
        skipped = tc.find("skipped")
        err = tc.find("error")
        if fail is not None or err is not None:
            node = fail if fail is not None else err
            detail = re.sub(r"\s+", " ", (node.text or node.get("message") or "")).strip()
            checks.append({"id": pkg, "verdict": "FAIL",
                           "criterion": name, "observed": detail[:300]})
        elif skipped is not None:
            checks.append({"id": pkg, "verdict": "SKIP",
                           "criterion": name, "observed": "skipped by h2spec"})
        else:
            checks.append({"id": pkg, "verdict": "PASS",
                           "criterion": name, "observed": ""})
    return checks


def run_h2_suite(serve):
    sid, title = "h2", "HTTP/2 h2c conformance (h2spec 2.6.0: generic + RFC 7540 + RFC 7541)"
    if not os.path.exists(H2SPEC):
        return {"id": sid, "title": title, "status": "PENDING",
                "pass": 0, "fail": 0, "skip": 0, "checks": [],
                "note": "h2/bin/h2spec not landed yet"}
    try:
        sections = h2spec_sections()
    except Exception as e:
        return {"id": sid, "title": title, "status": "ERROR",
                "pass": 0, "fail": 0, "skip": 0, "checks": [],
                "note": f"could not enumerate h2spec sections: {e}"}
    checks = []
    crashes = 0
    junit = os.path.join(HERE, f"scoreboard-h2spec-{PORT}.xml")
    for sec, ncases in sections:
        if not serve.ensure():
            checks.append({"id": sec, "verdict": "FAIL",
                           "criterion": f"section {sec} ({ncases} cases)",
                           "observed": "serve could not be (re)launched; section not run"})
            continue
        if os.path.exists(junit):
            os.remove(junit)
        try:
            subprocess.run([H2SPEC, sec, "-h", HOST, "-p", str(PORT),
                            "-o", "3", "-j", junit],
                           capture_output=True, text=True, timeout=180)
        except subprocess.TimeoutExpired:
            checks.append({"id": sec, "verdict": "FAIL",
                           "criterion": f"section {sec} ({ncases} cases)",
                           "observed": "h2spec timed out (180s)"})
            continue
        got = parse_junit(junit, sec)
        if not serve.alive():
            crashes += 1
            for c in got:
                if c["verdict"] == "FAIL":
                    c["observed"] = ("SERVE PROCESS DIED during this section; " +
                                     c["observed"])[:300]
        if got:
            checks.extend(got)
        else:
            checks.append({"id": sec, "verdict": "FAIL",
                           "criterion": f"section {sec} ({ncases} cases)",
                           "observed": "h2spec produced no junit results"})
    if os.path.exists(junit):
        os.remove(junit)
    # A parent section run (e.g. http2/5.1) also executes its subsections
    # (5.1.1, 5.1.2), which then run again as their own leaves — dedupe by
    # (package, case), keeping the LAST occurrence (the dedicated leaf run,
    # which had its own fresh serve-liveness check).
    seen = {}
    for c in checks:
        seen[(c["id"], c["criterion"])] = c
    checks = list(seen.values())
    note = f"{len(sections)} sections; serve process died in {crashes} section(s)" \
        if crashes else f"{len(sections)} sections"
    return {"id": sid, "title": title, "status": "RAN",
            "pass": sum(1 for c in checks if c["verdict"] == "PASS"),
            "fail": sum(1 for c in checks if c["verdict"] == "FAIL"),
            "skip": sum(1 for c in checks if c["verdict"] == "SKIP"),
            "checks": checks, "note": note}


def pending_dir_suite(sid, title, subdir, runner_names):
    """A directory suite that has not landed a runner yet."""
    d = os.path.join(HERE, subdir)
    runner = None
    if os.path.isdir(d):
        for name in runner_names:
            if os.path.exists(os.path.join(d, name)):
                runner = os.path.join(d, name)
                break
    if runner is None:
        note = (f"{subdir}/ present but no runner ({'/'.join(runner_names)}) yet"
                if os.path.isdir(d) else f"{subdir}/ not landed yet")
        return {"id": sid, "title": title, "status": "PENDING",
                "pass": 0, "fail": 0, "skip": 0, "checks": [], "note": note}
    # A runner landed: drive it with the standard env and scan for fresh results.
    env = dict(os.environ)
    env["CONF_HTTP_HOST"] = HOST
    env["CONF_HTTP_PORT"] = str(PORT)
    start = time.time()
    try:
        p = subprocess.run([PYTHON, runner], cwd=HERE, env=env,
                           capture_output=True, text=True, timeout=900)
    except subprocess.TimeoutExpired:
        return {"id": sid, "title": title, "status": "ERROR",
                "pass": 0, "fail": 0, "skip": 0, "checks": [],
                "note": f"{runner} timed out (900s)"}
    for base in (d, HERE):
        for fn in sorted(os.listdir(base)):
            if fn.endswith(".json"):
                got = parse_results_json(os.path.join(base, fn), start)
                if got:
                    checks = [{"id": c.get("id", "?"),
                               "verdict": c.get("verdict", "FAIL"),
                               "criterion": c.get("criterion", ""),
                               "observed": c.get("observed", "")}
                              for c in got["checks"]]
                    return {"id": sid, "title": title, "status": "RAN",
                            "pass": sum(1 for c in checks if c["verdict"] == "PASS"),
                            "fail": sum(1 for c in checks if c["verdict"] == "FAIL"),
                            "skip": sum(1 for c in checks
                                        if c["verdict"] not in ("PASS", "FAIL")),
                            "checks": checks, "note": f"via {os.path.basename(runner)}"}
    return {"id": sid, "title": title, "status": "ERROR",
            "pass": 0, "fail": 0, "skip": 0, "checks": [],
            "note": f"{os.path.basename(runner)} ran (exit={p.returncode}) "
                    "but wrote no parseable results json"}


# ---------------------------------------------------------------------------
# Aggregation + report
# ---------------------------------------------------------------------------
def write_scoreboard(suites, meta):
    graded = sum(s["pass"] + s["fail"] for s in suites)
    npass = sum(s["pass"] for s in suites)
    nfail = sum(s["fail"] for s in suites)
    nskip = sum(s["skip"] for s in suites)
    rate = (100.0 * npass / graded) if graded else 0.0

    lines = []
    lines.append("# Conformance scoreboard — deployed serve")
    lines.append("")
    lines.append(f"*Generated by `conformance/scoreboard.py` at {meta['generated']} "
                 f"against `{meta['target']}` (io={meta['io']}, "
                 f"binary mtime {meta['binary_mtime']}). Every number below comes "
                 f"from checks actually executed in this run; a FAIL is a mapped "
                 f"gap, not an error in the harness.*")
    lines.append("")
    lines.append("## Totals")
    lines.append("")
    lines.append(f"| total graded checks | pass | fail | pass-rate | skipped | serve launches |")
    lines.append(f"|---:|---:|---:|---:|---:|---:|")
    lines.append(f"| **{graded}** | **{npass}** | **{nfail}** | **{rate:.1f}%** "
                 f"| {nskip} | {meta['serve_launches']} |")
    lines.append("")
    lines.append("## Per-suite breakdown")
    lines.append("")
    lines.append("| suite | status | graded | pass | fail | skip | pass-rate | note |")
    lines.append("|---|---|---:|---:|---:|---:|---:|---|")
    for s in suites:
        g = s["pass"] + s["fail"]
        r = f"{100.0 * s['pass'] / g:.1f}%" if g else "—"
        lines.append(f"| {s['id']} — {s['title']} | {s['status']} | {g} | "
                     f"{s['pass']} | {s['fail']} | {s['skip']} | {r} | {s['note']} |")
    lines.append("")
    pend = [s for s in suites if s["status"] == "PENDING"]
    if pend:
        lines.append("Pending suites are not counted in any total; they will fold "
                     "in automatically once their runners land.")
        lines.append("")
    lines.append("## Gap list (every FAIL across every suite — the master to-do)")
    lines.append("")
    any_fail = False
    for s in suites:
        fails = [c for c in s["checks"] if c["verdict"] == "FAIL"]
        if not fails:
            continue
        any_fail = True
        lines.append(f"### {s['id']} ({len(fails)} failing)")
        lines.append("")
        for c in fails:
            obs = c["observed"].replace("|", "\\|")
            crit = c["criterion"].replace("|", "\\|")
            lines.append(f"- **{c['id']}** — {crit}")
            if obs:
                lines.append(f"  - observed: {obs}")
        lines.append("")
    if not any_fail:
        lines.append("*(no failing checks in this run — treat with suspicion and "
                     "add harder checks)*")
        lines.append("")
    skips = [(s["id"], c) for s in suites for c in s["checks"]
             if c["verdict"] not in ("PASS", "FAIL")]
    if skips:
        lines.append("## Skipped checks")
        lines.append("")
        for sid, c in skips:
            lines.append(f"- {sid} / **{c['id']}** — {c['criterion']}: {c['observed']}")
        lines.append("")

    md = "\n".join(lines) + "\n"
    with open(os.path.join(HERE, "SCOREBOARD.md"), "w") as f:
        f.write(md)
    out = {"generated": meta["generated"], "target": meta["target"],
           "io": meta["io"], "binary_mtime": meta["binary_mtime"],
           "serve_launches": meta["serve_launches"],
           "total_graded": graded, "pass": npass, "fail": nfail,
           "skip": nskip, "pass_rate": round(rate, 1),
           "suites": suites}
    with open(os.path.join(HERE, "results_scoreboard.json"), "w") as f:
        json.dump(out, f, indent=2)
    return graded, npass, nfail, nskip, rate


def main():
    if not os.path.exists(BINARY):
        print(f"ERROR: serve binary not found: {BINARY}", file=sys.stderr)
        sys.exit(2)
    serve = Serve()
    # Attribution guard: the port must be OURS alone. If something already
    # listens there, the verdicts could describe a serve this run did not
    # launch — refuse rather than score an unknown instance.
    try:
        probe = socket.create_connection((HOST, PORT), timeout=1.0)
        probe.close()
        print(f"ERROR: {HOST}:{PORT} is already in use — pick a free port "
              f"(CONF_SCOREBOARD_PORT) so every verdict is attributable to "
              f"the serve this run launches", file=sys.stderr)
        sys.exit(2)
    except OSError:
        pass
    print(f"[scoreboard] launching dedicated serve on {HOST}:{PORT} (io={IO})")
    if not serve.launch():
        print("ERROR: could not launch the serve", file=sys.stderr)
        sys.exit(2)
    suites = []
    try:
        print("[scoreboard] rfc-core ...")
        serve.ensure()
        suites.append(run_python_suite(
            "rfc-core", "HTTP/1.1 base conformance (RFC 7230/7231)",
            os.path.join(HERE, "rfc_conformance.py"), "results_rfc.json"))
        print("[scoreboard] rfc-full ...")
        serve.ensure()
        suites.append(run_python_suite(
            "rfc-full", "HTTP/1.1 full conformance (extended coverage)",
            os.path.join(HERE, "rfc_conformance_full.py"), "results_rfc_full.json"))
        print("[scoreboard] h2 (h2spec, section-by-section) ...")
        suites.append(run_h2_suite(serve))
        print("[scoreboard] ws ...")
        serve.ensure()
        suites.append(pending_dir_suite(
            "ws", "WebSocket conformance (RFC 6455)", "ws",
            ["run.py", "ws_conformance.py", "suite.py"]))
        print("[scoreboard] differential ...")
        serve.ensure()
        suites.append(pending_dir_suite(
            "diff", "Differential conformance vs reference origin", "differential",
            ["run.py", "differential.py", "suite.py"]))
        # ext LAST: its resource-limit group is destructive by design.
        print("[scoreboard] rfc-ext (destructive="
              f"{DESTRUCTIVE}) — runs last ...")
        serve.ensure()
        suites.append(run_python_suite(
            "rfc-ext", "HTTP/1.1 extended conformance (RFC 7230/31/32/33)",
            os.path.join(HERE, "rfc_conformance_ext.py"), "results_rfc_ext.json",
            {"CONF_DESTRUCTIVE": DESTRUCTIVE}))
    finally:
        serve.stop()

    meta = {
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "target": f"{HOST}:{PORT}",
        "io": IO,
        "binary_mtime": time.strftime("%Y-%m-%dT%H:%M:%S",
                                      time.localtime(os.path.getmtime(BINARY))),
        "serve_launches": serve.launches,
    }
    graded, npass, nfail, nskip, rate = write_scoreboard(suites, meta)

    print(f"\n== UNIFIED CONFORMANCE SCOREBOARD — {meta['target']} ==\n")
    for s in suites:
        g = s["pass"] + s["fail"]
        r = f"{100.0 * s['pass'] / g:5.1f}%" if g else "    —"
        print(f"  {s['id']:<9} {s['status']:<8} {s['pass']:>4}/{g:<4} {r}   {s['note']}")
    print(f"\n  TOTAL: {npass}/{graded} graded checks pass ({rate:.1f}%), "
          f"{nfail} failing (mapped gaps), {nskip} skipped")
    print(f"  wrote {os.path.join(HERE, 'SCOREBOARD.md')}")
    print(f"  wrote {os.path.join(HERE, 'results_scoreboard.json')}")


if __name__ == "__main__":
    main()
