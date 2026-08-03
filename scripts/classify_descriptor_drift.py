#!/usr/bin/env python3
"""classify_descriptor_drift.py — THE DRIFT-TAXONOMY CLASSIFIER.

Answers the one operational question a devnet upgrade asks: *does this descriptor
change need a WIPE (re-genesis), or is it a cheap tail-append?* It compares an OLD
descriptor set against a NEW one and emits the CLASS of the delta:

  UNCHANGED       — the two descriptor sets are semantically byte-identical.
  TAIL-APPEND     — cheap, NO re-genesis. New descriptor rows appended at the tail
                    (and/or new PI bindings at pi_index >= PI_PREFIX on an existing
                    member), while every existing member keeps its geometry: the
                    trace_width is unchanged AND the shared [0..PI_PREFIX) PI-prefix
                    binding map is untouched AND no member was removed/reordered.
  GEOMETRY-WIDEN  — a re-genesis FLAG-DAY. Some existing cohort member's geometry
                    moved: its trace_width changed, or its shared [0..PI_PREFIX)
                    PI-prefix binding map changed, or a member was removed/reordered,
                    or an existing member's fingerprint moved for any other reason
                    (a semantic change to a deployed member). Re-pins fingerprints
                    → the deployed cohort VK bytes move → every light client must
                    re-key → the chain must be re-genesised.

WHY THESE SIGNALS (grounded in docs/deos/VK-EPOCH-PLAN-2026-07-05.md §5-6, §9.2 and
docs/DEVNET-UPGRADE-AND-TREASURY-DIRECTIONS.md §2):
  - TAIL-APPEND is defined there as "new descriptor rows at the tail, the [0..46) PI
    prefix untouched, the cohort's descriptors byte-identical, no re-genesis".
    withMintHashPin (a single .piBinding at pi_index 46, the FIRST tail slot, with
    trace_width unchanged) is the canonical example — an EXISTING member changed
    bytes yet stayed a tail-append because it only added a binding in the tail region.
  - GEOMETRY-WIDEN is defined there as "trace_width / carrier geometry moves →
    re-pins fingerprints → an eyes-open re-genesis, ember-gated". The GENTIAN
    whole-cohort refuse-weld (§9.2, trace_width 1581 -> 1626 across all 36 members)
    is the canonical example.

So the DECISIVE, cheaply-extractable signals are exactly the two the plan names:
`trace_width` and the shared `[0..PI_PREFIX)` PI-binding map — plus cohort
membership and order (a removed/reordered member also moves the deployed VKs).

INPUT (a "descriptor set" = a directory tree, e.g. circuit/descriptors/):
  Every `*.json` file is one descriptor (the whole file is the descriptor JSON).
  Every `*.tsv` file is a registry: one `key<TAB>name<TAB>json` row per member.
Descriptors are keyed by their wire identity json["name"]; registries additionally
carry an ordered member list per file so a reorder is detectable.

USAGE:
  classify_descriptor_drift.py --old OLD_DIR --new NEW_DIR [--allow-regenesis]
  classify_descriptor_drift.py --old-ref GITREF --new NEW_DIR [--allow-regenesis]
      (--old-ref materializes GITREF:circuit/descriptors via `git show` into a temp dir)
  Options: --pi-prefix N (default 46) · --descriptors-subpath P
           (default circuit/descriptors, used with --old-ref) · --json (machine output)

EXIT CODES:
  0 = UNCHANGED or TAIL-APPEND, or GEOMETRY-WIDEN WITH --allow-regenesis (eyes-open).
  4 = GEOMETRY-WIDEN and --allow-regenesis was NOT given — REFUSED (a wipe-requiring
      change must not ship silently).
  2 = usage / IO / parse error.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

DEFAULT_PI_PREFIX = 46  # the shared [0..46) PI prefix every cohort member pins.
EXIT_REFUSED = 4
EXIT_ERR = 2


# ---- descriptor model -------------------------------------------------------

@dataclass
class Descriptor:
    key: str                    # STABLE identity: the artifact slot ("<file>" or
                                # "<file>#<rowkey>"). NOT json["name"] — the wire name
                                # collides across IR levels (e.g. attenuateA-v1 lives in
                                # both dregg-effectvm-attenuateA-v1.json and -attenuate-ir2.json).
    name: str                   # the wire name (json["name"]); a display attribute only.
    trace_width: int | None
    public_input_count: int | None
    prefix_bindings: frozenset  # {(pi_index, col, row)} for pi_index < PI_PREFIX
    tail_pi_indices: frozenset  # {pi_index >= PI_PREFIX} that carry a binding
    fingerprint: str            # sha256 of the canonical (sort_keys) descriptor JSON
    source: str                 # provenance for diagnostics (== key, human-facing)


@dataclass
class DescriptorSet:
    by_key: dict[str, Descriptor] = field(default_factory=dict)
    # per-registry-file ordered member-KEY lists (to detect reorder / removal-in-place)
    registry_order: dict[str, list[str]] = field(default_factory=dict)


def _canonical(obj) -> str:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"))


def _pi_bindings(desc_json: dict) -> list[tuple[int, int, str]]:
    """Extract every (pi_index, col, row) from the descriptor's pi_binding constraints."""
    out = []
    for c in desc_json.get("constraints", []) or []:
        if isinstance(c, dict) and c.get("t") == "pi_binding":
            pi = c.get("pi_index")
            if pi is None:
                continue
            out.append((int(pi), int(c.get("col", -1)), str(c.get("row", ""))))
    return out


def _mk_descriptor(desc_json: dict, key: str, pi_prefix: int) -> Descriptor:
    name = desc_json.get("name")
    if not isinstance(name, str):
        raise ValueError(f"descriptor at {key} has no string 'name'")
    binds = _pi_bindings(desc_json)
    prefix = frozenset(b for b in binds if b[0] < pi_prefix)
    tail = frozenset(b[0] for b in binds if b[0] >= pi_prefix)
    fp = hashlib.sha256(_canonical(desc_json).encode()).hexdigest()
    return Descriptor(
        key=key,
        name=name,
        trace_width=desc_json.get("trace_width"),
        public_input_count=desc_json.get("public_input_count"),
        prefix_bindings=prefix,
        tail_pi_indices=tail,
        fingerprint=fp,
        source=key,
    )


def load_descriptor_set(root: Path, pi_prefix: int) -> DescriptorSet:
    if not root.is_dir():
        raise ValueError(f"not a directory: {root}")
    ds = DescriptorSet()

    def add(desc: Descriptor):
        prev = ds.by_key.get(desc.key)
        if prev is not None and prev.fingerprint != desc.fingerprint:
            raise ValueError(
                f"descriptor slot {desc.key!r} appears twice with DIFFERENT bytes "
                f"— ambiguous descriptor set"
            )
        ds.by_key[desc.key] = desc

    for p in sorted(root.rglob("*")):
        if not p.is_file():
            continue
        rel = str(p.relative_to(root))
        if p.suffix == ".json":
            # PROVENANCE.json is the regen-control stamp, not a descriptor.
            if p.name == "PROVENANCE.json":
                continue
            try:
                obj = json.loads(p.read_text())
            except json.JSONDecodeError as e:
                raise ValueError(f"{rel}: invalid JSON ({e})")
            # ⚑ A FAMILY artifact is a JSON ARRAY of descriptor objects, not one object.
            # `circuit/descriptors/table-airs/dregg-ir2-exact-public-v1.json` (landed 17b138e1f,
            # rendered by `emitTableAirFamilyJson`, Dregg2/Circuit/TableAirIR.lean:782) is 64
            # arity-indexed members in one file. The `isinstance(obj, dict)` test below SKIPPED it
            # in silence — 64 members' geometry invisible to this gate, which is the shape of "a
            # gate that cannot go red". Members are keyed `<rel>#<index>`, the same `<file>#<row>`
            # convention the .tsv registry branch already uses, so the key stays the artifact SLOT.
            if isinstance(obj, list):
                for i, member in enumerate(obj):
                    if not isinstance(member, dict) or "name" not in member:
                        continue
                    add(_mk_descriptor(member, f"{rel}#{i}", pi_prefix))
                continue
            if not isinstance(obj, dict) or "name" not in obj:
                continue  # not a descriptor object
            add(_mk_descriptor(obj, rel, pi_prefix))
        elif p.suffix == ".tsv":
            order: list[str] = []
            for lineno, raw in enumerate(p.read_text().splitlines(), 1):
                if not raw.strip():
                    continue
                parts = raw.split("\t")
                if len(parts) < 3:
                    continue
                rowkey, _name, js = parts[0], parts[1], parts[2]
                try:
                    obj = json.loads(js)
                except json.JSONDecodeError as e:
                    raise ValueError(f"{rel}:{lineno}: invalid row JSON ({e})")
                if not isinstance(obj, dict) or "name" not in obj:
                    continue
                desc = _mk_descriptor(obj, f"{rel}#{rowkey}", pi_prefix)
                add(desc)
                order.append(desc.key)
            if order:
                ds.registry_order[rel] = order
    return ds


# ---- classification ---------------------------------------------------------

TAIL_APPEND = "TAIL-APPEND"
GEOMETRY_WIDEN = "GEOMETRY-WIDEN"
UNCHANGED = "UNCHANGED"


@dataclass
class Verdict:
    klass: str
    geometry_widen_reasons: list[str] = field(default_factory=list)
    tail_append_reasons: list[str] = field(default_factory=list)
    added: list[str] = field(default_factory=list)
    removed: list[str] = field(default_factory=list)
    changed_geo: list[str] = field(default_factory=list)     # existing member geometry moved
    changed_tail: list[str] = field(default_factory=list)    # existing member changed only in tail
    pi_prefix: int = DEFAULT_PI_PREFIX


def classify(old: DescriptorSet, new: DescriptorSet, pi_prefix: int) -> Verdict:
    v = Verdict(klass=UNCHANGED, pi_prefix=pi_prefix)

    old_keys = set(old.by_key)
    new_keys = set(new.by_key)

    # 1. Membership: removed members force a re-genesis (the deployed cohort shrank /
    #    a descriptor slot vanished → every verifier that pinned it must re-key).
    for key in sorted(old_keys - new_keys):
        v.removed.append(key)
        v.geometry_widen_reasons.append(
            f"member REMOVED: {key!r} (name {old.by_key[key].name!r}) — a deployed "
            f"descriptor disappeared; the cohort fingerprint set moves"
        )

    # 2. Added members are the tail-append case (staged new rows).
    for key in sorted(new_keys - old_keys):
        v.added.append(key)
        v.tail_append_reasons.append(
            f"member ADDED: {key!r} (name {new.by_key[key].name!r})"
        )

    # 3. Shared members: compare geometry (trace_width + [0..PI_PREFIX) prefix map).
    for key in sorted(old_keys & new_keys):
        o = old.by_key[key]
        n = new.by_key[key]
        if o.fingerprint == n.fingerprint:
            continue  # byte-identical member — the stable cohort core.

        geo_moved = False
        if o.trace_width != n.trace_width:
            geo_moved = True
            v.geometry_widen_reasons.append(
                f"trace_width MOVED on {key!r}: {o.trace_width} -> {n.trace_width} "
                f"(carrier geometry widened → fingerprint re-pin → re-genesis)"
            )
        if o.prefix_bindings != n.prefix_bindings:
            geo_moved = True
            added_p = sorted(n.prefix_bindings - o.prefix_bindings)
            dropped_p = sorted(o.prefix_bindings - n.prefix_bindings)
            v.geometry_widen_reasons.append(
                f"shared [0..{pi_prefix}) PI-prefix binding map CHANGED on {key!r}: "
                f"+{added_p} -{dropped_p} (the prefix every cohort member pins moved)"
            )

        if geo_moved:
            v.changed_geo.append(key)
            continue

        # trace_width + prefix are stable, but the bytes moved. It is a TAIL-APPEND
        # only if the sole change is additive in the tail region (new pi_index >=
        # PI_PREFIX bindings). Any OTHER byte change to a deployed member (a new/edited
        # gate on existing columns) re-pins its fingerprint with no geometry signal to
        # justify calling it cheap — treat it conservatively as a re-genesis item.
        new_tail = sorted(n.tail_pi_indices - o.tail_pi_indices)
        lost_tail = sorted(o.tail_pi_indices - n.tail_pi_indices)
        purely_tail_pi = bool(new_tail) and not lost_tail and o.public_input_count is not None \
            and n.public_input_count is not None and n.public_input_count >= o.public_input_count
        if purely_tail_pi:
            v.changed_tail.append(key)
            v.tail_append_reasons.append(
                f"member {key!r} gained tail PI binding(s) at pi_index {new_tail} "
                f"(>= {pi_prefix}), trace_width + [0..{pi_prefix}) prefix unchanged "
                f"(a withMintHashPin-style additive pin)"
            )
        else:
            v.changed_geo.append(key)
            v.geometry_widen_reasons.append(
                f"existing member {key!r} FINGERPRINT re-pinned with no tail-only "
                f"justification (bytes changed, trace_width + prefix stable, but the "
                f"change is not a pure tail PI append) — a deployed member moved; "
                f"treat as re-genesis"
            )

    # 4. Registry ORDER: within each shared registry file, the old member order must be
    #    an in-order prefix of the new order. A reorder shifts every downstream member's
    #    position in the recursive registry hash → re-genesis.
    for rel, old_order in old.registry_order.items():
        new_order = new.registry_order.get(rel)
        if new_order is None:
            continue
        # old order, restricted to members still present, must appear as an in-order
        # prefix of new order.
        surviving = [k for k in old_order if k in new.by_key]
        if new_order[: len(surviving)] != surviving:
            v.geometry_widen_reasons.append(
                f"registry {rel}: existing members were REORDERED (old order is not an "
                f"in-order prefix of the new order) — member positions shifted → re-genesis"
            )

    # Final class.
    if v.geometry_widen_reasons:
        v.klass = GEOMETRY_WIDEN
    elif v.tail_append_reasons:
        v.klass = TAIL_APPEND
    else:
        v.klass = UNCHANGED
    return v


# ---- CLI --------------------------------------------------------------------

def _materialize_ref(ref: str, subpath: str) -> Path:
    """Extract <ref>:<subpath> (a directory) into a temp dir via git, return its path.
    The temp dir is intentionally NOT cleaned here (process-lifetime); the OS reaps it."""
    tmp = Path(tempfile.mkdtemp(prefix="drift-taxonomy-old."))
    try:
        listing = subprocess.run(
            ["git", "ls-tree", "-r", "--name-only", f"{ref}:{subpath}"],
            check=True, capture_output=True, text=True,
        ).stdout.splitlines()
    except subprocess.CalledProcessError as e:
        sys.exit(f"classify_descriptor_drift: cannot read {ref}:{subpath} from git "
                 f"({e.stderr.strip() or e})")
    for rel in listing:
        if not rel:
            continue
        # `git cat-file --filters`, NOT `git show`: the descriptors include seven
        # LFS-tracked staged-registry TSVs, and `git show` does NOT run the LFS
        # smudge filter — it writes the ~132-byte POINTER. The NEW side reads the
        # working tree, which `actions/checkout --lfs` smudged to real content, so
        # the OLD side parsed ZERO members from exactly the DEPLOYED effect-VM
        # descriptors (transfer/mint/burn/noteSpend R24) and their 194 members all
        # looked like phantom tail-ADDs on every run: an IDENTICAL tree classified
        # TAIL-APPEND and exited 0 instead of UNCHANGED. Worse, that made the gate's
        # entire purpose unreachable for that cohort — a GEOMETRY-WIDEN (re-genesis
        # flag-day) looks like an ADD when the old member was never parsed, so exit 4
        # could not fire. `--filters` applies the smudge filter, so OLD and NEW are
        # compared in the same representation. (`lfs: true` on checkout does not help:
        # smudge applies at checkout, not to `git show`.)
        blob = subprocess.run(
            ["git", "cat-file", "--filters", f"{ref}:{subpath}/{rel}"],
            check=True, capture_output=True,
        ).stdout
        dst = tmp / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_bytes(blob)
    return tmp


def render_human(v: Verdict) -> str:
    lines = [f"drift-taxonomy: CLASS = {v.klass}"]
    n_shared_stable = None
    if v.added:
        lines.append(f"  + {len(v.added)} member(s) ADDED at the tail")
    if v.changed_tail:
        lines.append(f"  ~ {len(v.changed_tail)} existing member(s) gained tail PI bindings (additive)")
    if v.changed_geo:
        lines.append(f"  ! {len(v.changed_geo)} existing member(s) with MOVED geometry / re-pinned fingerprint")
    if v.removed:
        lines.append(f"  - {len(v.removed)} member(s) REMOVED")
    if v.klass == GEOMETRY_WIDEN:
        lines.append("  WHY re-genesis is required:")
        for r in v.geometry_widen_reasons[:40]:
            lines.append(f"    · {r}")
        if len(v.geometry_widen_reasons) > 40:
            lines.append(f"    · … and {len(v.geometry_widen_reasons) - 40} more")
    elif v.klass == TAIL_APPEND:
        lines.append("  cheap tail-append (no re-genesis); additions:")
        for r in v.tail_append_reasons[:40]:
            lines.append(f"    · {r}")
        if len(v.tail_append_reasons) > 40:
            lines.append(f"    · … and {len(v.tail_append_reasons) - 40} more")
    return "\n".join(lines)


def main() -> None:
    ap = argparse.ArgumentParser(description="Classify a descriptor-set delta (drift taxonomy).")
    ap.add_argument("--old", type=Path, help="OLD descriptor-set directory")
    ap.add_argument("--old-ref", help="git ref; materialize <ref>:<descriptors-subpath> as OLD")
    ap.add_argument("--new", type=Path, required=True, help="NEW descriptor-set directory")
    ap.add_argument("--descriptors-subpath", default="circuit/descriptors",
                    help="subpath used with --old-ref (default circuit/descriptors)")
    ap.add_argument("--pi-prefix", type=int, default=DEFAULT_PI_PREFIX,
                    help=f"shared PI-prefix boundary (default {DEFAULT_PI_PREFIX})")
    ap.add_argument("--allow-regenesis", action="store_true",
                    help="acknowledge an eyes-open re-genesis; permits a GEOMETRY-WIDEN to pass")
    ap.add_argument("--json", action="store_true", help="emit the verdict as JSON")
    args = ap.parse_args()

    if bool(args.old) == bool(args.old_ref):
        sys.exit("classify_descriptor_drift: give exactly one of --old / --old-ref")

    try:
        old_root = args.old if args.old else _materialize_ref(args.old_ref, args.descriptors_subpath)
        old = load_descriptor_set(old_root, args.pi_prefix)
        new = load_descriptor_set(args.new, args.pi_prefix)
    except ValueError as e:
        sys.exit(f"classify_descriptor_drift: {e}")

    v = classify(old, new, args.pi_prefix)

    if args.json:
        print(json.dumps({
            "class": v.klass,
            "pi_prefix": v.pi_prefix,
            "added": v.added,
            "removed": v.removed,
            "changed_geometry": v.changed_geo,
            "changed_tail_only": v.changed_tail,
            "geometry_widen_reasons": v.geometry_widen_reasons,
            "tail_append_reasons": v.tail_append_reasons,
            "old_member_count": len(old.by_key),
            "new_member_count": len(new.by_key),
        }, indent=2))
    else:
        print(render_human(v))

    if v.klass == GEOMETRY_WIDEN and not args.allow_regenesis:
        sys.stderr.write(
            "\ndrift-taxonomy: REFUSED — this is a GEOMETRY-WIDEN (re-genesis flag-day):\n"
            "  an existing cohort member's geometry moved, so the deployed VK bytes change\n"
            "  and every light client must re-key. A change that requires a WIPE must not\n"
            "  ship silently. To proceed EYES-OPEN (you have planned the re-genesis:\n"
            "  new committee keys → new federation_id → fresh chain, old data-dir archived),\n"
            "  re-run with --allow-regenesis.\n"
        )
        sys.exit(EXIT_REFUSED)


if __name__ == "__main__":
    main()
