#!/usr/bin/env python3
"""Integrity and interpretation gates for the stability-v2 artifact."""

from __future__ import annotations

import csv
import hashlib
import pathlib


ROOT = pathlib.Path(__file__).resolve().parent


def verify_checksums() -> None:
    expected: dict[pathlib.Path, str] = {}
    for line in (ROOT / "SHA256SUMS").read_text(encoding="utf-8").splitlines():
        digest, name = line.split("  ", 1)
        expected[pathlib.Path(name)] = digest
    actual = {
        path.relative_to(ROOT)
        for path in ROOT.rglob("*")
        if path.is_file() and path.name != "SHA256SUMS" and "__pycache__" not in path.parts
    }
    if set(expected) != actual:
        raise ValueError(f"checksum census mismatch: missing={actual-set(expected)}, stale={set(expected)-actual}")
    for path, digest in expected.items():
        observed = hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
        if observed != digest:
            raise ValueError(f"SHA-256 mismatch: {path}")


def verify_canonical_proofs() -> dict[tuple[str, str], bytes]:
    first: dict[tuple[str, str], bytes] = {}
    tampers = []
    with (ROOT / "proof-byte-manifest.csv").open(newline="", encoding="utf-8") as handle:
        for row in csv.reader(handle):
            if len(row) < 7 or row[0] == "workload":
                continue
            if row[2] == "honest-proof":
                key = (row[0], row[1])
                path = ROOT / "proofs-canonical" / f"{row[0]}-{row[1]}-{row[3]}.postcard"
                data = path.read_bytes()
                if len(data) != int(row[4]):
                    raise ValueError(f"proof length mismatch: {path}")
                if key in first and data != first[key]:
                    raise ValueError(f"nondeterministic canonical repeat: {key}")
                first[key] = data
            elif row[2] == "public-input-tamper":
                tampers.append(row[6])
    if len(first) != 8 or tampers != ["consumer_verifier_rejected"] * 8:
        raise ValueError("canonical proof/tamper census failed")
    return first


def verify_sweep(canonical: dict[tuple[str, str], bytes]) -> None:
    first: dict[tuple[str, str, str], bytes] = {}
    counts: dict[tuple[str, str, str], int] = {}
    with (ROOT / "transcript-sweep-raw.csv").open(newline="", encoding="utf-8") as handle:
        for row in csv.reader(handle):
            if not row or row[0] != "SWEEP":
                continue
            key = (row[1], row[2], row[3])
            path = ROOT / "proofs-transcript-sweep" / f"{row[1]}-{row[2]}-{row[3]}-{row[4]}.postcard"
            data = path.read_bytes()
            if len(data) != int(row[6]):
                raise ValueError(f"sweep proof length mismatch: {path}")
            if key in first and data != first[key]:
                raise ValueError(f"nondeterministic sweep repeat: {key}")
            first[key] = data
            counts[key] = counts.get(key, 0) + 1
    if len(first) != 26 or set(counts.values()) != {10}:
        raise ValueError("sweep endpoint/repetition census failed")
    # Byte-for-byte bridge from the canonical semantic names to the same sweep
    # assignments.  This also guards the separate recompilation/run.
    bridge = {
        ("admission", "source"): ("admission", "expiry-none", "source"),
        ("admission", "optimized"): ("admission", "expiry-none", "optimized"),
        ("upgrade", "source"): ("branch", "right", "source"),
        ("upgrade", "optimized"): ("branch", "right", "optimized"),
        ("clearance", "source"): ("branch", "left", "source"),
        ("clearance", "optimized"): ("branch", "left", "optimized"),
        ("strand", "source"): ("strand", "seed", "source"),
        ("strand", "optimized"): ("strand", "seed", "optimized"),
    }
    for canonical_key, sweep_key in bridge.items():
        if canonical[canonical_key] != first[sweep_key]:
            raise ValueError(f"canonical/sweep proof mismatch: {canonical_key}")
    for assignment in ("seed", "vouch", "bond", "seed-vouch", "seed-bond", "vouch-bond", "all"):
        if first[("strand", assignment, "source")] != first[("strand", assignment, "optimized")]:
            raise ValueError(f"Strand byte-identical control failed: {assignment}")


def verify_shapes_and_interpretation() -> None:
    inputs = ROOT / "inputs" / "generated"
    if (inputs / "upgrade-source.descriptor.json").read_bytes() != (inputs / "clearance-source.descriptor.json").read_bytes():
        raise ValueError("Upgrade/Clearance source shape drift")
    if (inputs / "upgrade-optimized.descriptor.json").read_bytes() != (inputs / "clearance-optimized.descriptor.json").read_bytes():
        raise ValueError("Upgrade/Clearance optimized shape drift")
    with (ROOT / "paired-summary.csv").open(newline="", encoding="utf-8") as handle:
        paired = list(csv.DictReader(handle))
    if any(row["general_speedup_claim"] != "false" for row in paired):
        raise ValueError("fixed-transcript table leaked a general speedup claim")
    with (ROOT / "transcript-sweep-summary.csv").open(newline="", encoding="utf-8") as handle:
        sweep = list(csv.DictReader(handle))
    admission = [float(row["optimized_over_source"]) for row in sweep if row["shape"] == "admission"]
    if not (min(admission) < 1 < max(admission)):
        raise ValueError("Admission direction-reversal canary did not fire")
    with (ROOT / "transcript-sweep-shape-summary.csv").open(
        newline="", encoding="utf-8"
    ) as handle:
        shapes = list(csv.DictReader(handle))
    if any(float(row["pow_witness_time_pearson"]) < 0.98 for row in shapes):
        raise ValueError("query-PoW witness/timing correlation canary did not fire")
    strand = next(row for row in shapes if row["shape"] == "strand")
    if strand["pow_witness_time_spearman"] != "1.000000":
        raise ValueError("Strand witness/timing rank canary did not fire")
    with (ROOT / "verifier-transcript-sweep-shape-summary.csv").open(
        newline="", encoding="utf-8"
    ) as handle:
        verifier_shapes = {row["shape"]: row for row in csv.DictReader(handle)}
    stable = "STABLE_OPT_FASTER_ACROSS_COMPLETE_ACCEPTING_CENSUS"
    if verifier_shapes["admission"]["verdict"] != stable:
        raise ValueError("Admission verifier-census stability gate failed")
    if verifier_shapes["branch"]["verdict"] != stable:
        raise ValueError("branch verifier-census stability gate failed")
    if verifier_shapes["strand"]["verdict"] != "BYTE_IDENTICAL_NULL_OK":
        raise ValueError("Strand verifier-census null gate failed")


def main() -> None:
    canonical = verify_canonical_proofs()
    verify_sweep(canonical)
    verify_shapes_and_interpretation()
    verify_checksums()
    print("stability-v2 artifact: all integrity and interpretation gates passed")


if __name__ == "__main__":
    main()
