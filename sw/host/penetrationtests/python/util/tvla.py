# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import math


def welch_t_stat(group_a: list[int], group_b: list[int]) -> float:
    """Compute Welch's two-sample t-statistic between two sample groups."""
    n_a = len(group_a)
    n_b = len(group_b)
    if n_a < 2 or n_b < 2:
        return 0.0
    mean_a = sum(group_a) / n_a
    mean_b = sum(group_b) / n_b
    var_a = sum((x - mean_a) ** 2 for x in group_a) / (n_a - 1)
    var_b = sum((x - mean_b) ** 2 for x in group_b) / (n_b - 1)
    denom_sq = (var_a / n_a) + (var_b / n_b)
    if denom_sq <= 0.0:
        return 0.0 if mean_a == mean_b else float("inf")
    return (mean_a - mean_b) / math.sqrt(denom_sq)


def welch_t_stat_detrended(samples: list[int], labels: list[int]) -> float:
    """Compute drift-cancelled Welch's t-statistic across disjoint adjacent (0,1) vs (1,0) pairs."""
    n = min(len(samples), len(labels))
    grp_01 = []
    grp_10 = []
    i = 0
    while i + 1 < n:
        l0, l1 = labels[i], labels[i + 1]
        if l0 != l1:
            diff = samples[i + 1] - samples[i]
            if l0 == 0 and l1 == 1:
                grp_01.append(diff)
            else:
                grp_10.append(diff)
            i += 2
        else:
            i += 1
    if len(grp_01) >= 2 and len(grp_10) >= 2:
        return welch_t_stat(grp_01, grp_10)
    fixed = [s for s, lbl in zip(samples[:n], labels[:n]) if lbl == 1]
    random_grp = [s for s, lbl in zip(samples[:n], labels[:n]) if lbl == 0]
    return welch_t_stat(fixed, random_grp)


def compute_fvsr_tvla(batch: dict, fvsr_labels: list[int]) -> dict:
    """Compute Fixed-vs-Random Welch's t-test on a sensor batch dictionary."""
    channels = ("mcycle_deltas", "clock_drift")
    t_stats = {}
    n = min(len(fvsr_labels), batch["num_samples"])
    lbls = fvsr_labels[:n]
    for channel in channels:
        samples = batch[channel][:n]
        if channel == "mcycle_deltas":
            fixed = [s for s, lbl in zip(samples, lbls) if lbl == 1]
            random_grp = [s for s, lbl in zip(samples, lbls) if lbl == 0]
            t_stats[channel] = welch_t_stat(fixed, random_grp)
        else:
            t_stats[channel] = welch_t_stat_detrended(samples, lbls)
    batch["t_stats"] = t_stats
    return batch
