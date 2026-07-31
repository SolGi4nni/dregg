#!/usr/bin/env python3
"""lean-ffi-closure.py — enumerate the module closure of the ONE runtime splice root.

Prints one module name per line for the transitive import closure of
`Dregg2.FFI` — THE Lean<->Rust boundary manifest, and the same single target
`dregg-lean-ffi/build.rs` builds and splices — walking BOTH the project tree and
every lake package (mathlib's module syntax — `public import` / `private import`
/ `meta import` / `import all` — included). Core (Init/Lean/Std) modules come
from the toolchain, not the seed, and are skipped.

⚠ The prose here said "the executor roots and the six real post-quantum runtime
roots" until 2026-07-30. That was true of the NINE-ROOT LIST this file carried
until `ec4ed5e17` and false of the code under it for a day afterwards — a name
outliving the thing it named, which is how the nine-root list survived review in
the first place.

TWO consumers, and they must not drift:
  * `dregg-lean-ffi/scripts/seed-dregg2-closure.sh` picks the seed's members
    from this list. Archiving every warm IR object ships ~5000 mathlib modules
    the FFI never imports (a 295 MB seed where the closure is ~96 MB — measured
    2026-07-10, docs/LEAN-SEED-SIZE.md).
  * `scripts/check-lean-seed-closure.sh` checks an archive AGAINST this list, so
    a seed and its check compute the closure the same way by construction. That
    gate is what detects a disagreement with `build.rs::boundary_closure`, the
    third walk of this same graph (Rust, in-tree edges only) — see its note.

Usage: lean-ffi-closure.py <metatheory-dir> [extra roots...]
"""
import re
import sys
from pathlib import Path

meta = Path(sys.argv[1] if len(sys.argv) > 1 else "metatheory")
# ⚑ ONE ROOT — `Dregg2.FFI`, THE SAME ONE `dregg-lean-ffi/build.rs` builds and splices.
#
# This was a hand-maintained 9-root list until 2026-07-29, and it was a strict SUBSET of
# `Dregg2/FFI.lean`'s import closure: 95 modules short, every one of them a verified DECISION
# (all five light-client gates, the finality gate, cross-cell conservation, R3Verify, the storage
# content root, strand admission, DelegAdmit, both game oracles). A seed cut from this list can
# never carry those exports no matter how often it is regenerated — which is exactly what
# `docs/ASSESS-cold-build-silent-export.md` §4 measured and misread as "splice-only".
#
# `Dregg2/FFI.lean` is the boundary manifest and exists to abolish lists like the one that stood
# here. Extra roots can still be passed on argv for a one-off.
ROOTS = [
    "Dregg2.FFI",
]
ROOTS += sys.argv[2:]

pkg_roots = [meta] + sorted((meta / ".lake/packages").glob("*"))
IMP = re.compile(r"^(?:public\s+|private\s+|meta\s+)*import\s+(?:all\s+)?([\w.«»]+)", re.M)


def mod2file(m: str):
    rel = m.replace(".", "/") + ".lean"
    for root in pkg_roots:
        p = root / rel
        if p.exists():
            return p
    return None


seen, queue = set(), [r for r in ROOTS]
while queue:
    m = queue.pop()
    if m in seen:
        continue
    f = mod2file(m)
    if f is None:
        continue  # toolchain-provided (Init/Lean/Std) — not a seed member
    seen.add(m)
    queue.extend(IMP.findall(f.read_text(encoding="utf-8")))

for m in sorted(seen):
    print(m)
