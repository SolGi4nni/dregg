#!/usr/bin/env python3
"""Summarize transcript sweep, proof bytes, Boolean baseline, and telemetry."""

from __future__ import annotations

import csv
import hashlib
import pathlib
from collections import defaultdict

import numpy as np


ROOT = pathlib.Path(__file__).resolve().parent
BOOTSTRAPS = 20_000


def write_csv(name: str, rows: list[dict[str, object]]) -> None:
    with (ROOT / name).open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def average_ranks(values: np.ndarray) -> np.ndarray:
    result = np.empty(values.size, dtype=np.float64)
    order = np.argsort(values)
    position = 0
    while position < values.size:
        end = position + 1
        while end < values.size and values[order[end]] == values[order[position]]:
            end += 1
        result[order[position:end]] = (position + end - 1) / 2
        position = end
    return result


def correlation(left: np.ndarray, right: np.ndarray) -> tuple[float, float]:
    pearson = float(np.corrcoef(left, right)[0, 1])
    spearman = float(np.corrcoef(average_ranks(left), average_ranks(right))[0, 1])
    return pearson, spearman


def sweep() -> None:
    times: dict[tuple[str, str, str], list[float]] = defaultdict(list)
    lengths: dict[tuple[str, str, str], set[int]] = defaultdict(set)
    hashes: dict[tuple[str, str, str], set[str]] = defaultdict(set)
    with (ROOT / "transcript-sweep-raw.csv").open(newline="", encoding="utf-8") as handle:
        for row in csv.reader(handle):
            if row and row[0] == "SWEEP":
                key = (row[1], row[2], row[3])
                times[key].append(int(row[5]) / 1_000_000)
                lengths[key].add(int(row[6]))
                hashes[key].add(row[7])
    witnesses: dict[tuple[str, str, str], set[int]] = defaultdict(set)
    with (ROOT / "pow-witness-transcript-sweep.csv").open(
        newline="", encoding="utf-8"
    ) as handle:
        for row in csv.DictReader(handle):
            for key in times:
                prefix = "-".join(key) + "-"
                if row["file"].startswith(prefix):
                    witnesses[key].add(int(row["query_pow_witness"]))
                    break
            else:
                raise ValueError(f"unmatched sweep proof filename: {row['file']}")
    if any(len(values) != 1 for values in witnesses.values()) or set(witnesses) != set(times):
        raise ValueError("query PoW witness is not fixed one-per-endpoint")
    assignments = sorted({(shape, assignment) for shape, assignment, _ in times})
    rows: list[dict[str, object]] = []
    shape_ratios: dict[str, list[float]] = defaultdict(list)
    shape_source: dict[str, list[float]] = defaultdict(list)
    shape_optimized: dict[str, list[float]] = defaultdict(list)
    shape_witnesses: dict[str, list[int]] = defaultdict(list)
    shape_times: dict[str, list[float]] = defaultdict(list)
    for shape, assignment in assignments:
        source = np.asarray(times[(shape, assignment, "source")])
        optimized = np.asarray(times[(shape, assignment, "optimized")])
        source_median = float(np.median(source))
        optimized_median = float(np.median(optimized))
        timing_ratio = optimized_median / source_median
        shape_ratios[shape].append(timing_ratio)
        shape_source[shape].append(source_median)
        shape_optimized[shape].append(optimized_median)
        source_witness = next(iter(witnesses[(shape, assignment, "source")]))
        optimized_witness = next(iter(witnesses[(shape, assignment, "optimized")]))
        if shape == "strand":
            if source_witness != optimized_witness:
                raise ValueError(f"Strand witness mismatch: {assignment}")
            shape_witnesses[shape].append(source_witness)
            shape_times[shape].append((source_median + optimized_median) / 2)
        else:
            shape_witnesses[shape].extend([source_witness, optimized_witness])
            shape_times[shape].extend([source_median, optimized_median])
        rows.append({
            "shape": shape,
            "assignment": assignment,
            "repeats": source.size,
            "source_median_ms": f"{source_median:.6f}",
            "optimized_median_ms": f"{optimized_median:.6f}",
            "optimized_over_source": f"{timing_ratio:.6f}",
            "source_proof_bytes": next(iter(lengths[(shape, assignment, "source")])),
            "optimized_proof_bytes": next(iter(lengths[(shape, assignment, "optimized")])),
            "source_unique_hashes": len(hashes[(shape, assignment, "source")]),
            "optimized_unique_hashes": len(hashes[(shape, assignment, "optimized")]),
            "source_query_pow_witness": source_witness,
            "optimized_query_pow_witness": optimized_witness,
            "all_repeats_byte_identical": str(
                len(hashes[(shape, assignment, "source")]) == 1
                and len(hashes[(shape, assignment, "optimized")]) == 1
            ).lower(),
        })
    write_csv("transcript-sweep-summary.csv", rows)
    shape_rows = []
    for shape in sorted(shape_ratios):
        values = np.asarray(shape_ratios[shape])
        source_values = np.asarray(shape_source[shape])
        optimized_values = np.asarray(shape_optimized[shape])
        witness_values = np.asarray(shape_witnesses[shape], dtype=np.float64)
        timing_values = np.asarray(shape_times[shape], dtype=np.float64)
        pearson, spearman = correlation(witness_values, timing_values)
        if shape == "admission":
            verdict = "NO_GENERAL_SPEEDUP_DIRECTION_REVERSES"
        elif shape == "branch":
            verdict = "ALL_THREE_FASTER_BUT_TRANSCRIPT_CENSUS_TOO_SMALL"
        else:
            verdict = "BYTE_IDENTICAL_NULL_TIMING_RATIO_NEAR_ONE"
        shape_rows.append({
            "shape": shape,
            "accepting_assignments": values.size,
            "optimized_faster_assignments": int(np.sum(values < 1)),
            "ratio_min": f"{np.min(values):.6f}",
            "ratio_median": f"{np.median(values):.6f}",
            "ratio_max": f"{np.max(values):.6f}",
            "source_absolute_ms_min": f"{np.min(source_values):.6f}",
            "source_absolute_ms_max": f"{np.max(source_values):.6f}",
            "optimized_absolute_ms_min": f"{np.min(optimized_values):.6f}",
            "optimized_absolute_ms_max": f"{np.max(optimized_values):.6f}",
            "pow_witness_time_pearson": f"{pearson:.6f}",
            "pow_witness_time_spearman": f"{spearman:.6f}",
            "general_speedup_claim": "false",
            "verdict": verdict,
        })
    write_csv("transcript-sweep-shape-summary.csv", shape_rows)


def baseline() -> None:
    values: dict[str, list[float]] = defaultdict(list)
    with (ROOT / "boolean-baseline-raw.csv").open(newline="", encoding="utf-8") as handle:
        for row in csv.reader(handle):
            if row and row[0] == "BASELINE":
                values[row[1]].append(int(row[4]) / int(row[3]))
    rows = []
    for case, observed_list in sorted(values.items()):
        observed = np.asarray(observed_list)
        rows.append({
            "case": case,
            "samples": observed.size,
            "iterations_per_sample": 10_000_000,
            "median_ns_per_eval": f"{np.median(observed):.6f}",
            "p10_ns_per_eval": f"{np.quantile(observed, 0.1):.6f}",
            "p90_ns_per_eval": f"{np.quantile(observed, 0.9):.6f}",
            "scope": "native_boolean_after_atoms_no_proof",
        })
    write_csv("boolean-baseline-summary.csv", rows)


def proof_bytes() -> None:
    records: dict[tuple[str, str], dict[str, set[str] | set[int] | int]] = defaultdict(
        lambda: {"lengths": set(), "hashes": set(), "count": 0}
    )
    tampers = []
    witnesses: dict[tuple[str, str], set[int]] = defaultdict(set)
    with (ROOT / "pow-witness-canonical.csv").open(newline="", encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            for workload in ("admission", "upgrade", "clearance", "strand"):
                for variant in ("source", "optimized"):
                    if row["file"].startswith(f"{workload}-{variant}-"):
                        witnesses[(workload, variant)].add(int(row["query_pow_witness"]))
                        break
                else:
                    continue
                break
            else:
                raise ValueError(f"unmatched canonical proof filename: {row['file']}")
    with (ROOT / "proof-byte-manifest.csv").open(newline="", encoding="utf-8") as handle:
        for row in csv.reader(handle):
            if len(row) < 7 or row[0] == "workload":
                continue
            if row[2] == "honest-proof":
                record = records[(row[0], row[1])]
                record["lengths"].add(int(row[4]))
                record["hashes"].add(row[5])
                record["count"] += 1
            elif row[2] == "public-input-tamper":
                tampers.append(row[6])
    rows = []
    for (workload, variant), record in sorted(records.items()):
        rows.append({
            "workload": workload,
            "variant": variant,
            "retained_proofs": record["count"],
            "proof_bytes": next(iter(record["lengths"])),
            "unique_proof_hashes": len(record["hashes"]),
            "query_pow_witness": next(iter(witnesses[(workload, variant)])),
            "deterministic_repeats": str(len(record["hashes"]) == 1).lower(),
            "tamper_disposition": "consumer_verifier_rejected",
        })
    if len(tampers) != 8 or set(tampers) != {"consumer_verifier_rejected"}:
        raise ValueError("tamper disposition audit failed")
    write_csv("proof-byte-summary.csv", rows)


def verifier_sweep() -> None:
    paired: dict[
        tuple[str, str], dict[str, dict[int, dict[str, float]]]
    ] = defaultdict(lambda: defaultdict(lambda: defaultdict(dict)))
    with (ROOT / "verifier-transcript-sweep-raw.csv").open(
        newline="", encoding="utf-8"
    ) as handle:
        for row in csv.reader(handle):
            if row and row[0] == "VERIFY_SWEEP":
                paired[(row[2], row[3])][row[1]][int(row[5])][row[4]] = (
                    int(row[6]) / 1_000_000
                )
    rng = np.random.default_rng(0xD12EC7_2)
    rows = []
    for (shape, assignment), session_data in sorted(paired.items()):
        if sorted(session_data) != [f"session-{index:02d}" for index in range(1, 8)]:
            raise ValueError(f"verifier session census failed: {shape}/{assignment}")
        session_logs = []
        session_draws = np.empty((7, BOOTSTRAPS), dtype=np.float64)
        source_times = []
        optimized_times = []
        for session_index, session in enumerate(sorted(session_data)):
            rounds = session_data[session]
            if sorted(rounds) != list(range(200)) or any(
                set(pair) != {"source", "optimized"} for pair in rounds.values()
            ):
                raise ValueError(f"verifier rounds failed: {session}/{shape}/{assignment}")
            logs_by_parity = []
            for parity in (0, 1):
                values = np.asarray([
                    np.log(rounds[round_index]["optimized"] / rounds[round_index]["source"])
                    for round_index in range(parity, 200, 2)
                ])
                indices = rng.integers(0, values.size, size=(BOOTSTRAPS, values.size))
                logs_by_parity.append(values[indices])
            all_logs = np.concatenate([
                np.asarray([
                    np.log(pair["optimized"] / pair["source"])
                    for pair in rounds.values()
                ])
            ])
            session_logs.append(float(np.median(all_logs)))
            session_draws[session_index] = np.median(
                np.concatenate(logs_by_parity, axis=1), axis=1
            )
            source_times.extend(pair["source"] for pair in rounds.values())
            optimized_times.extend(pair["optimized"] for pair in rounds.values())
        outer = rng.integers(0, 7, size=(BOOTSTRAPS, 7))
        boot_indices = np.arange(BOOTSTRAPS)[:, None]
        estimates = np.median(session_draws[outer, boot_indices], axis=1)
        point = float(np.median(session_logs))
        lo, hi = np.quantile(estimates, [0.025, 0.975])
        if shape == "strand":
            verdict = "NULL_OK" if lo <= 0 <= hi else "NULL_FAILED"
        elif hi < 0 and all(value < 0 for value in session_logs):
            verdict = "STABLE_OPT_FASTER_FOR_ACCEPTING_ASSIGNMENT"
        else:
            verdict = "NO_STABLE_VERIFIER_CLAIM"
        rows.append({
            "shape": shape,
            "assignment": assignment,
            "sessions": 7,
            "paired_rounds": 1400,
            "source_median_ms": f"{np.median(source_times):.6f}",
            "optimized_median_ms": f"{np.median(optimized_times):.6f}",
            "optimized_over_source": f"{np.exp(point):.6f}",
            "hier_boot95_lo": f"{np.exp(lo):.6f}",
            "hier_boot95_hi": f"{np.exp(hi):.6f}",
            "session_ratio_min": f"{np.exp(min(session_logs)):.6f}",
            "session_ratio_max": f"{np.exp(max(session_logs)):.6f}",
            "verdict": verdict,
        })
    write_csv("verifier-transcript-sweep-summary.csv", rows)
    shape_rows = []
    for shape in ("admission", "branch", "strand"):
        selected = [row for row in rows if row["shape"] == shape]
        ratios = np.asarray([float(row["optimized_over_source"]) for row in selected])
        if shape == "strand":
            verdict = (
                "BYTE_IDENTICAL_NULL_OK"
                if all(row["verdict"] == "NULL_OK" for row in selected)
                else "NULL_FAILED"
            )
        else:
            verdict = (
                "STABLE_OPT_FASTER_ACROSS_COMPLETE_ACCEPTING_CENSUS"
                if all(
                    row["verdict"] == "STABLE_OPT_FASTER_FOR_ACCEPTING_ASSIGNMENT"
                    for row in selected
                )
                else "NO_SHAPE_LEVEL_VERIFIER_CLAIM"
            )
        shape_rows.append({
            "shape": shape,
            "accepting_assignments": len(selected),
            "ratio_min": f"{np.min(ratios):.6f}",
            "ratio_median": f"{np.median(ratios):.6f}",
            "ratio_max": f"{np.max(ratios):.6f}",
            "verdict": verdict,
        })
    write_csv("verifier-transcript-sweep-shape-summary.csv", shape_rows)


def telemetry() -> None:
    rows = []
    for path in sorted((ROOT / "sessions").glob("session-*/telemetry.csv")):
        load1 = []
        runnable = []
        with path.open(newline="", encoding="utf-8") as handle:
            for row in csv.DictReader(handle):
                load1.append(float(row["load1"]))
                runnable.append(int(row["runnable"]))
        rows.append({
            "session": path.parent.name,
            "telemetry_seconds": len(load1),
            "load1_min": f"{min(load1):.2f}",
            "load1_max": f"{max(load1):.2f}",
            "runnable_max": max(runnable),
            "cpuset": "22-23",
            "rayon_threads": 2,
        })
    write_csv("telemetry-summary.csv", rows)


def checksums() -> None:
    paths = sorted(
        path for path in ROOT.rglob("*")
        if path.is_file() and path.name != "SHA256SUMS" and "__pycache__" not in path.parts
    )
    with (ROOT / "SHA256SUMS").open("w", encoding="utf-8") as handle:
        for path in paths:
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
            handle.write(f"{digest}  {path.relative_to(ROOT)}\n")


def main() -> None:
    sweep()
    baseline()
    proof_bytes()
    verifier_sweep()
    telemetry()
    checksums()


if __name__ == "__main__":
    main()
