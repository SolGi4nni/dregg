#!/usr/bin/env python3
"""The Lean module closure that `libdrorb.a` is cut from — computed ONCE, here.

`ffi/build-dataplane-lib.sh` needs this list to build every module's
`:c.o.export` object; `scripts/archive-freshness.sh` needs it to decide whether
the archive on disk is older than any source it was cut from. Those two lists
must be the SAME list, so it lives in one file rather than being copy-pasted into
the freshness gate (a copy would rot the first time a seam is added, and the
symptom would be a gate that silently stops covering the new module).

Output: one module name per line, sorted, only modules with a real `.lean` file.

    scripts/dataplane-closure.py                 the archive BUILD closure
    scripts/dataplane-closure.py --all-roots     ... plus every module the build
                                                 script compiles by an explicit
                                                 `lake build <M>:c.o.export` line
                                                 (parsed out of the script, so it
                                                 cannot drift), and their imports
    scripts/dataplane-closure.py --files         print `.lean` paths instead

WHY `--all-roots` exists and the build does not use it: the build script's
explicit `lake build X:c.o.export` lines already emit those objects, so adding
them to the loop's list would change nothing about what is built — but they ARE
sources the archive depends on, so the FRESHNESS gate must watch them. Keeping
the build's own list byte-identical means this refactor cannot change what gets
archived.
"""
import argparse
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BUILD_SCRIPT = os.path.join(ROOT, "ffi", "build-dataplane-lib.sh")

# The archive BUILD seeds. `Dataplane` is the serve closure proper; the rest are
# export roots reached only from the host's own threads (they are archived
# because the `find` step globs every `.c.o.export`, and their `initialize_*`
# references pull their imports), so they must be walked too or a FROM-SCRATCH
# host link fails undefined. Kept verbatim from the heredoc this file replaced.
SEEDS = [
    "Dataplane",
    "Client.FetchExport",
    "Client.H2Receive",
    "Client.Fetch",
    "Client.H2",
    "Body.FrameRaw",
    "Ws.Decode",
    "Ws.ReassemblyAdmit",
    "Ws.ReassemblyClose",
    "Ws.Encode",
]

IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_.]+)", re.M)
EXPLICIT_ROOT_RE = re.compile(r"\+?([A-Za-z0-9_.]+):c\.o\.export")


def module_path(mod):
    return os.path.join(ROOT, mod.replace(".", "/") + ".lean")


def imports(mod):
    p = module_path(mod)
    if not os.path.exists(p):
        return []
    with open(p, encoding="utf-8", errors="replace") as f:
        return IMPORT_RE.findall(f.read())


def explicit_roots():
    """Every module the archive build compiles by name. Parsed from the build
    script itself, so a new `lake build Foo:c.o.export` line is covered by the
    freshness gate the moment it is added — no second list to keep in step."""
    if not os.path.exists(BUILD_SCRIPT):
        return []
    with open(BUILD_SCRIPT, encoding="utf-8", errors="replace") as f:
        return EXPLICIT_ROOT_RE.findall(f.read())


def closure(seeds):
    seen, stack = set(), list(seeds)
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        stack += imports(m)
    return sorted(m for m in seen if os.path.exists(module_path(m)))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--all-roots", action="store_true",
                    help="also seed from the build script's explicit :c.o.export roots")
    ap.add_argument("--files", action="store_true", help="print .lean paths")
    args = ap.parse_args()

    seeds = list(SEEDS)
    if args.all_roots:
        seeds += explicit_roots()
    mods = closure(seeds)
    if not mods:
        print("dataplane-closure: EMPTY closure — wrong root?", file=sys.stderr)
        return 1
    for m in mods:
        print(module_path(m) if args.files else m)
    return 0


if __name__ == "__main__":
    sys.exit(main())
