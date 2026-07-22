#!/usr/bin/env python3
"""Robust paired analysis for the direct-logic stability-v2 campaign.

The benchmark alternates source/optimized execution order on every round.  We
therefore analyze within-round log ratios, retain order parity as a stratum,
and resample whole process sessions before resampling pairs.  Strand is a
byte-identical source/optimized negative control.
"""

from __future__ import annotations

import csv
import hashlib
import math
import pathlib
import sys
from collections import defaultdict

import numpy as np


ROOT = pathlib.Path(__file__).resolve().parent
SESSIONS = ROOT / "sessions"
BOOTSTRAPS = 20_000
SEED = 0xD12EC7
NULL_MATERIALITY = 0.05


def q(values: np.ndarray, probability: float) -> float:
    return float(np.quantile(values, probability))


def ratio(log_value: float) -> float:
    return math.exp(log_value)


def load_sessions() -> tuple[
    dict[str, dict[tuple[str, str, int], dict[str, int]]],
    dict[str, dict[tuple[str, str], dict[str, str]]],
    dict[str, list[tuple[str, str, str, str]]],
]:
    samples: dict[str, dict[tuple[str, str, int], dict[str, int]]] = {}
    workloads: dict[str, dict[tuple[str, str], dict[str, str]]] = {}
    tampers: dict[str, list[tuple[str, str, str, str]]] = {}
    paths = sorted(SESSIONS.glob("session-*/raw.log"))
    if not paths:
        raise SystemExit(f"no session logs below {SESSIONS}")
    for path in paths:
        session = path.parent.name
        session_samples: dict[tuple[str, str, int], dict[str, int]] = defaultdict(dict)
        session_workloads: dict[tuple[str, str], dict[str, str]] = {}
        session_tampers: list[tuple[str, str, str, str]] = []
        with path.open(newline="", encoding="utf-8") as handle:
            for row in csv.reader(handle):
                if not row:
                    continue
                if row[0] == "SAMPLE":
                    workload, variant, stage, round_s, elapsed_s = row[1:6]
                    key = (workload, stage, int(round_s))
                    if variant in session_samples[key]:
                        raise ValueError(f"{session}: duplicate sample {key}/{variant}")
                    session_samples[key][variant] = int(elapsed_s)
                elif row[0] == "WORKLOAD":
                    workload, variant = row[1:3]
                    session_workloads[(workload, variant)] = {
                        "atoms": row[3],
                        "width": row[4],
                        "public": row[5],
                        "constraints": row[6],
                        "multiplications": row[7],
                        "auxiliaries": row[8],
                        "descriptor_bytes": row[9],
                        "descriptor_blake3": row[10],
                        "proof_bytes": row[11],
                        "degree_bits": row[12],
                    }
                elif row[0] == "TAMPER":
                    session_tampers.append(tuple(row[1:5]))
        for key, pair in session_samples.items():
            if set(pair) != {"source", "optimized"}:
                raise ValueError(f"{session}: incomplete source/optimized pair {key}: {pair}")
        for workload in ("admission", "upgrade", "clearance", "strand"):
            for stage, expected in (("prove", 30), ("verify", 100)):
                rounds = sorted(
                    round_index
                    for candidate, candidate_stage, round_index in session_samples
                    if candidate == workload and candidate_stage == stage
                )
                if rounds != list(range(expected)):
                    raise ValueError(
                        f"{session}: {workload}/{stage} rounds are not exactly 0..{expected - 1}"
                    )
        if len(session_tampers) != 8 or any(t[-1] != "verifier_rejected" for t in session_tampers):
            raise ValueError(f"{session}: expected eight consumer-verifier tamper refusals")
        if len(session_workloads) != 8:
            raise ValueError(f"{session}: expected eight workload records")
        samples[session] = dict(session_samples)
        workloads[session] = session_workloads
        tampers[session] = session_tampers
    return samples, workloads, tampers


def logs_for(
    samples: dict[str, dict[tuple[str, str, int], dict[str, int]]],
    session: str,
    workload: str,
    stage: str,
    parity: int | None = None,
) -> np.ndarray:
    result = []
    for (candidate, candidate_stage, round_index), pair in samples[session].items():
        if candidate != workload or candidate_stage != stage:
            continue
        if parity is not None and round_index % 2 != parity:
            continue
        result.append(math.log(pair["optimized"] / pair["source"]))
    return np.asarray(result, dtype=np.float64)


def hierarchical_bootstrap(
    samples: dict[str, dict[tuple[str, str, int], dict[str, int]]],
    workload: str,
    stage: str,
    rng: np.random.Generator,
    adjust_control: bool,
) -> np.ndarray:
    sessions = sorted(samples)
    # `session_draws[i, b]` is inner bootstrap b for process session i.
    # Building all B draws with NumPy indexing avoids treating a slow Python
    # loop as part of the benchmark campaign itself.
    session_draws = np.empty((len(sessions), BOOTSTRAPS), dtype=np.float64)
    for session_index, session in enumerate(sessions):
        target_parts = []
        control_parts = []
        for parity in (0, 1):
            target = logs_for(samples, session, workload, stage, parity)
            indices = rng.integers(0, target.size, size=(BOOTSTRAPS, target.size))
            target_parts.append(target[indices])
            if adjust_control:
                control = logs_for(samples, session, "strand", stage, parity)
                control_indices = rng.integers(
                    0, control.size, size=(BOOTSTRAPS, control.size)
                )
                control_parts.append(control[control_indices])
        estimates = np.median(np.concatenate(target_parts, axis=1), axis=1)
        if adjust_control:
            estimates -= np.median(np.concatenate(control_parts, axis=1), axis=1)
        session_draws[session_index] = estimates
    outer = rng.integers(
        0, len(sessions), size=(BOOTSTRAPS, len(sessions))
    )
    boot_indices = np.arange(BOOTSTRAPS)[:, None]
    return np.median(session_draws[outer, boot_indices], axis=1)


def check_layouts(workloads: dict[str, dict[tuple[str, str], dict[str, str]]]) -> None:
    first = workloads[sorted(workloads)[0]]
    for session, records in workloads.items():
        for key, record in records.items():
            # Proof contents may alter postcard length.  All deterministic fields
            # must be identical across fresh-process sessions.
            for field in record:
                if field == "proof_bytes":
                    continue
                if record[field] != first[key][field]:
                    raise ValueError(f"{session}: deterministic field drift {key}/{field}")
    strand_source = first[("strand", "source")]
    strand_optimized = first[("strand", "optimized")]
    for field in (
        "atoms", "width", "public", "constraints", "multiplications",
        "auxiliaries", "descriptor_bytes", "descriptor_blake3",
    ):
        if strand_source[field] != strand_optimized[field]:
            raise ValueError(f"Strand negative control is not byte/resource identical: {field}")


def write_summary(
    samples: dict[str, dict[tuple[str, str, int], dict[str, int]]],
) -> list[dict[str, str]]:
    rng = np.random.default_rng(SEED)
    sessions = sorted(samples)
    rows: list[dict[str, str]] = []
    for stage in ("prove", "verify"):
        for workload in ("admission", "upgrade", "clearance", "strand"):
            session_logs = {
                session: logs_for(samples, session, workload, stage) for session in sessions
            }
            pooled = np.concatenate(list(session_logs.values()))
            session_medians = np.asarray(
                [float(np.median(session_logs[session])) for session in sessions]
            )
            raw_boot = hierarchical_bootstrap(samples, workload, stage, rng, False)
            raw_lo, raw_hi = q(raw_boot, 0.025), q(raw_boot, 0.975)
            raw_median = float(np.median(session_medians))
            if workload == "strand":
                adjusted_median = 0.0
                adjusted_lo = 0.0
                adjusted_hi = 0.0
            else:
                adjusted_boot = hierarchical_bootstrap(samples, workload, stage, rng, True)
                adjusted_lo, adjusted_hi = q(adjusted_boot, 0.025), q(adjusted_boot, 0.975)
                adjusted_median = float(
                    np.median([
                        np.median(session_logs[session])
                        - np.median(logs_for(samples, session, "strand", stage))
                        for session in sessions
                    ])
                )
            all_below = bool(np.all(session_medians < 0))
            all_above = bool(np.all(session_medians > 0))
            raw_excludes_one = raw_hi < 0 or raw_lo > 0
            adjusted_excludes_one = adjusted_hi < 0 or adjusted_lo > 0
            control_boot = hierarchical_bootstrap(samples, "strand", stage, rng, False)
            control_lo, control_hi = q(control_boot, 0.025), q(control_boot, 0.975)
            control_median = float(np.median([
                np.median(logs_for(samples, session, "strand", stage))
                for session in sessions
            ]))
            null_ok = (
                control_lo <= 0 <= control_hi
                and abs(ratio(control_median) - 1.0) <= NULL_MATERIALITY
            )
            if workload == "strand":
                verdict = "NULL_OK" if null_ok else "NULL_FAILED"
            elif (
                null_ok
                and raw_excludes_one
                and adjusted_excludes_one
                and (all_below or all_above)
            ):
                # Every repetition uses the same deterministic proof transcript.
                # This establishes clock stability for that transcript only;
                # the independent accepting-assignment sweep is the gate for any
                # generalized performance claim.
                verdict = (
                    "FIXED_TRANSCRIPT_OPT_FASTER"
                    if all_below else "FIXED_TRANSCRIPT_OPT_SLOWER"
                )
            else:
                verdict = "NO_STABLE_TIMING_CLAIM"
            rows.append({
                "workload": workload,
                "stage": stage,
                "sessions": str(len(sessions)),
                "pairs": str(pooled.size),
                "median_opt_over_source": f"{ratio(raw_median):.6f}",
                "hier_boot95_lo": f"{ratio(raw_lo):.6f}",
                "hier_boot95_hi": f"{ratio(raw_hi):.6f}",
                "control_adjusted_ratio": f"{ratio(adjusted_median):.6f}",
                "control_adjusted_boot95_lo": f"{ratio(adjusted_lo):.6f}",
                "control_adjusted_boot95_hi": f"{ratio(adjusted_hi):.6f}",
                "session_ratio_min": f"{ratio(float(np.min(session_medians))):.6f}",
                "session_ratio_max": f"{ratio(float(np.max(session_medians))):.6f}",
                "optimized_pair_win_rate": f"{float(np.mean(pooled < 0)):.6f}",
                "direction_unanimous": str(all_below or all_above).lower(),
                "strand_null_ok": str(null_ok).lower(),
                "fixed_transcript_only": "true",
                "general_speedup_claim": "false",
                "verdict": verdict,
            })
    fieldnames = list(rows[0])
    with (ROOT / "paired-summary.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)
    return rows


def write_session_summary(
    samples: dict[str, dict[tuple[str, str, int], dict[str, int]]],
) -> None:
    rows = []
    for session in sorted(samples):
        for stage in ("prove", "verify"):
            for workload in ("admission", "upgrade", "clearance", "strand"):
                values = logs_for(samples, session, workload, stage)
                rows.append({
                    "session": session,
                    "workload": workload,
                    "stage": stage,
                    "pairs": str(values.size),
                    "median_opt_over_source": f"{ratio(float(np.median(values))):.6f}",
                    "p10_ratio": f"{ratio(q(values, 0.10)):.6f}",
                    "p90_ratio": f"{ratio(q(values, 0.90)):.6f}",
                    "optimized_pair_win_rate": f"{float(np.mean(values < 0)):.6f}",
                })
    with (ROOT / "session-summary.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def write_checksums() -> None:
    paths = sorted(
        path for path in ROOT.rglob("*")
        if path.is_file() and path.name != "SHA256SUMS"
    )
    with (ROOT / "SHA256SUMS").open("w", encoding="utf-8") as handle:
        for path in paths:
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
            handle.write(f"{digest}  {path.relative_to(ROOT)}\n")


def main() -> None:
    samples, workloads, _tampers = load_sessions()
    check_layouts(workloads)
    rows = write_summary(samples)
    write_session_summary(samples)
    write_checksums()
    writer = csv.DictWriter(sys.stdout, fieldnames=list(rows[0]))
    writer.writeheader()
    writer.writerows(rows)


if __name__ == "__main__":
    main()
