#!/usr/bin/env python3
"""rebake-wrap-referee.py -- install `wrap-public-input.json` as WRAP_PUBLIC_INPUT_MEASURED.

    scripts/rebake-wrap-referee.py <out-dir>/wrap-public-input.json [--check]

═══ THE WOUND THIS CLOSES ══════════════════════════════════════════════════════════════════
`MinaWrapDeferredWords.WRAP_PUBLIC_INPUT_MEASURED` is THE REFEREE: the forty words openmina's own
`PreparedStatement::to_public_input(40)` produced, and the list every agreement count in this cone
is graded against -- `KimchiWrapMainPins12.the_forty_agree_but_for_slot_twelve` above all.
`pickles_kimchi_marshal` writes those words to `wrap-public-input.json`, and the hop from that file
into the tracked module was a MANUAL paste that no script performed.

⚠ That is the same shape as the `/tmp -> fixtures/` hop `regen-stepmain-fixtures.sh` exists to close,
and it has already cost this cone once: `WRAP_PUBLIC_INPUT_MEASURED` was baked on the wrong side of a
wrap re-emit and went stale **at exactly slot 12**, the one slot under investigation, while every
instrument kept reporting a count against it. A referee stale at the slot you are measuring is worse
than no referee.

⚑ WHAT THIS DOES NOT DO: it does not decide that a re-bake is correct. Re-baking makes every count
graded against the old list a count about an object that no longer exists, so the caller must
RE-MEASURE (`EmitWrapFortyAgreement`) and never read a previous number forward.
"""
import re
import sys
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
MODULE = ROOT / "metatheory/Dregg2/Circuit/Emit/MinaWrapDeferredWords.lean"
DEF = "def WRAP_PUBLIC_INPUT_MEASURED : List Nat :="


def render(slots):
    out = ["  ["]
    for k, s in enumerate(slots):
        tail = "" if k + 1 == len(slots) else ","
        out.append("   %s%s -- %2d  %s" % (s["value"], tail, s["i"], s["name"]))
    out.append("  ]")
    return "\n".join(out) + "\n"


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    check = "--check" in sys.argv
    if len(args) != 1:
        print(__doc__)
        return 2
    doc = json.loads(pathlib.Path(args[0]).read_text())
    slots = doc["slots"]
    # ⚑ FAIL CLOSED on an arity that is not the wrap key's. `prove_wrap` refuses any rung whose
    # `public_input_size` is not 40, and a referee of another length would silently re-index every
    # slot comparison downstream of it.
    if doc["npublic"] != 40 or len(slots) != 40:
        print("rebake-wrap-referee: %s carries %d words, not 40" % (args[0], len(slots)))
        return 1
    for k, s in enumerate(slots):
        if s["i"] != k:
            print("rebake-wrap-referee: slot %d is labelled %d" % (k, s["i"]))
            return 1

    src = MODULE.read_text()
    at = src.index(DEF) + len(DEF)
    open_at = src.index("  [", at)
    close_at = src.index("\n  ]\n", open_at) + len("\n  ]\n")
    new = src[:open_at] + render(slots) + src[close_at:]
    if new == src:
        print("rebake-wrap-referee: the tracked referee IS this run's forty (0 slots moved)")
        return 0

    old_vals = re.findall(r"^   (\d+)[,]?\s+--", src[open_at:close_at], re.M)
    moved = [k for k in range(40) if k >= len(old_vals) or old_vals[k] != slots[k]["value"]]
    if check:
        print("rebake-wrap-referee: ⚑ THE TRACKED REFEREE IS NOT THIS RUN'S FORTY")
        print("  %d of 40 slots differ: %s" % (len(moved), moved))
        return 1
    MODULE.write_text(new)
    print("rebake-wrap-referee: INSTALLED -- %d of 40 slots MOVED: %s" % (len(moved), moved))
    print("⚠ every count graded against the old list is now about an object that does not exist.")
    print("  RE-MEASURE, never read forward:")
    print("    cd metatheory && lake env lean --run Dregg2/Circuit/Emit/EmitWrapFortyAgreement.lean")
    return 0


if __name__ == "__main__":
    sys.exit(main())
