#!/usr/bin/env python3
"""Turn direct_logic_live_benchmark SAMPLE rows into the checked-in summary."""

import csv
import sys
from collections import defaultdict

import numpy as np


def main() -> None:
    raw_path = sys.argv[1] if len(sys.argv) > 1 else "raw.log"
    samples: dict[tuple[str, str], list[float]] = defaultdict(list)
    with open(raw_path, encoding="utf-8") as raw:
        for row in csv.reader(raw):
            if row and row[0] == "SAMPLE":
                samples[(row[1], row[2])].append(int(row[4]) / 1_000_000)

    print(
        "workload,stage,n,median_ms,p95_ms,mean_ms,stddev_ms,"
        "median_boot95_lo_ms,median_boot95_hi_ms,"
        "mean_boot95_lo_ms,mean_boot95_hi_ms,min_ms,max_ms"
    )
    for seed, (key, values) in enumerate(sorted(samples.items()), 1):
        observed = np.asarray(values, dtype=np.float64)
        rng = np.random.default_rng(seed)
        indices = rng.integers(0, observed.size, size=(10_000, observed.size))
        draws = observed[indices]
        bootstrap_medians = np.median(draws, axis=1)
        bootstrap_means = np.mean(draws, axis=1)
        median, p95 = np.quantile(observed, [0.5, 0.95])
        median_lo, median_hi = np.quantile(bootstrap_medians, [0.025, 0.975])
        mean_lo, mean_hi = np.quantile(bootstrap_means, [0.025, 0.975])
        print(
            f"{key[0]},{key[1]},{observed.size},{median:.6f},{p95:.6f},"
            f"{np.mean(observed):.6f},{np.std(observed, ddof=1):.6f},"
            f"{median_lo:.6f},{median_hi:.6f},{mean_lo:.6f},{mean_hi:.6f},"
            f"{np.min(observed):.6f},{np.max(observed):.6f}"
        )


if __name__ == "__main__":
    main()
