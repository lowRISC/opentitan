# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""General-purpose Test Vector Leakage Assessment (TVLA) statistical accumulator.

Provides an online two-group (Fixed vs. Random) Welch's t-test accumulator (``TVLA``)
that maintains running count, sum, and sum-of-squares statistics per sample key
(both scalar keys and vector keys) without storing raw traces in memory, along with
standard Hamming Weight and Hamming Distance leakage model helpers.
"""

from collections import defaultdict
from dataclasses import dataclass
import math
from typing import (
    Any,
    Dict,
    Hashable,
    Iterable,
    List,
    Mapping,
    Optional,
    Sequence,
    Tuple,
    Union,
)


def hamming_weight(val: int, width: Optional[int] = 32) -> int:
    """Return the Hamming weight (population count) of ``val``."""
    if width == 32:
        return bin(val & 0xFFFFFFFF).count("1")
    if width is not None:
        val &= (1 << width) - 1
    return bin(val).count("1")


def hamming_distance(a: int, b: int, width: Optional[int] = 32) -> int:
    """Return the Hamming distance between ``a`` and ``b``."""
    if width == 32:
        return bin((a ^ b) & 0xFFFFFFFF).count("1")
    return hamming_weight(a ^ b, width=width)


@dataclass(frozen=True)
class TVLAResult:
    """Welch's t-test result for a single sample key across Fixed (0) vs. Random (1) groups."""

    key: Hashable
    t_stat: float
    mean_fixed: float
    mean_random: float
    var_fixed: float
    var_random: float
    count_fixed: int
    count_random: int


def _new_scalar_acc() -> List[float]:
    return [0.0, 0.0, 0.0, 0.0, 0.0, 0.0]


class _VectorAcc:
    """Running Fixed (0) vs. Random (1) accumulators for a fixed-length vector."""

    __slots__ = ("count", "sum", "sum_sq")

    def __init__(self, length: int) -> None:
        self.count: List[int] = [0, 0]
        self.sum: List[List[float]] = [[0.0] * length, [0.0] * length]
        self.sum_sq: List[List[float]] = [[0.0] * length, [0.0] * length]

    def __getstate__(
        self,
    ) -> Tuple[List[int], List[List[float]], List[List[float]]]:
        return (self.count, self.sum, self.sum_sq)

    def __setstate__(
        self, state: Tuple[List[int], List[List[float]], List[List[float]]]
    ) -> None:
        self.count, self.sum, self.sum_sq = state


class TVLA:
    """General-purpose online Welch's t-test accumulator for Fixed-vs-Random TVLA.

    Supports both scalar sample keys (`add_sample`) and fixed-length vector keys
    (`add_vector`), maintaining running counts, sums, and sums-of-squares in O(1)
    memory per sample point.
    """

    def __init__(self, threshold: float = 7.0) -> None:
        self.threshold = threshold
        # Scalar accumulators: key -> [n0, sum0, sum_sq0, n1, sum1, sum_sq1]
        self._scalar_acc: Dict[Hashable, List[float]] = defaultdict(
            _new_scalar_acc
        )
        # Vector accumulators: key -> _VectorAcc
        self._vector_acc: Dict[Hashable, _VectorAcc] = {}
        self.trace_counts: List[int] = [0, 0]

    def reset(self) -> None:
        """Clear all accumulated statistics and trace counts."""
        self._scalar_acc.clear()
        self._vector_acc.clear()
        self.trace_counts = [0, 0]

    def merge(self, other: "TVLA") -> None:
        """Merge accumulated statistics from ``other`` into ``self``."""
        self.trace_counts[0] += other.trace_counts[0]
        self.trace_counts[1] += other.trace_counts[1]
        for key, other_acc in other._scalar_acc.items():
            acc = self._scalar_acc[key]
            for idx in range(6):
                acc[idx] += other_acc[idx]
        for key, other_vacc in other._vector_acc.items():
            vacc = self._vector_acc.get(key)
            if vacc is None:
                vacc = _VectorAcc(len(other_vacc.sum[0]))
                self._vector_acc[key] = vacc
            for grp in (0, 1):
                vacc.count[grp] += other_vacc.count[grp]
                s_arr = vacc.sum[grp]
                sq_arr = vacc.sum_sq[grp]
                other_s = other_vacc.sum[grp]
                other_sq = other_vacc.sum_sq[grp]
                for idx in range(len(s_arr)):
                    s_arr[idx] += other_s[idx]
                    sq_arr[idx] += other_sq[idx]

    @property
    def num_keys(self) -> int:
        """Return the number of distinct scalar and vector keys accumulated."""
        return len(self._scalar_acc) + len(self._vector_acc)

    def record_trace(self, group: int) -> None:
        """Increment the trace counter for ``group`` (``0``=Fixed, ``1``=Random)."""
        if group not in (0, 1):
            raise ValueError(f"TVLA group must be 0 (Fixed) or 1 (Random), got {group}")
        self.trace_counts[group] += 1

    def add_sample(self, key: Hashable, group: int, value: float) -> None:
        """Accumulate a single scalar ``value`` at ``key`` for ``group`` (``0`` or ``1``)."""
        if group not in (0, 1):
            raise ValueError(f"TVLA group must be 0 (Fixed) or 1 (Random), got {group}")
        acc = self._scalar_acc[key]
        base = 0 if group == 0 else 3
        fval = float(value)
        acc[base] += 1.0
        acc[base + 1] += fval
        acc[base + 2] += fval * fval

    def add_samples(
        self, group: int, samples: Iterable[Tuple[Hashable, float]]
    ) -> None:
        """Accumulate multiple ``(key, value)`` pairs for ``group`` (``0`` or ``1``)."""
        if group not in (0, 1):
            raise ValueError(f"TVLA group must be 0 (Fixed) or 1 (Random), got {group}")
        base = 0 if group == 0 else 3
        scalar_acc = self._scalar_acc
        for key, value in samples:
            acc = scalar_acc[key]
            fval = float(value)
            acc[base] += 1.0
            acc[base + 1] += fval
            acc[base + 2] += fval * fval

    def add_vector(
        self, key: Hashable, group: int, values: Sequence[float]
    ) -> None:
        """Accumulate a fixed-width sequence of ``values`` at ``key`` for ``group``."""
        if group not in (0, 1):
            raise ValueError(f"TVLA group must be 0 (Fixed) or 1 (Random), got {group}")
        n_elem = len(values)
        vacc = self._vector_acc.get(key)
        if vacc is None:
            vacc = _VectorAcc(n_elem)
            self._vector_acc[key] = vacc
        vacc.count[group] += 1
        s_arr = vacc.sum[group]
        sq_arr = vacc.sum_sq[group]
        for idx, val in enumerate(values):
            fval = float(val)
            s_arr[idx] += fval
            sq_arr[idx] += fval * fval

    def add_trace(
        self,
        group: int,
        trace: Union[Mapping[Hashable, float], Sequence[float]],
        key: Hashable = "trace",
    ) -> None:
        """Record one trace for ``group`` from either a key->value mapping or 1D sequence."""
        self.record_trace(group)
        if isinstance(trace, Mapping):
            self.add_samples(group, trace.items())
        else:
            self.add_vector(key, group, trace)

    @staticmethod
    def welch_t(
        n0: float,
        sum0: float,
        sum_sq0: float,
        n1: float,
        sum1: float,
        sum_sq1: float,
    ) -> Tuple[float, float, float, float, float]:
        """Compute Welch's two-sample t-statistic from summary accumulators.

        Returns:
            Tuple ``(t_stat, mean0, mean1, var0, var1)`` with sample variances
            computed using Bessel's correction (``ddof=1``).
        """
        if n0 < 2.0 or n1 < 2.0:
            return 0.0, 0.0, 0.0, 0.0, 0.0
        mean0 = sum0 / n0
        mean1 = sum1 / n1
        var0 = max(0.0, (sum_sq0 / n0) - (mean0 * mean0)) * (n0 / (n0 - 1.0))
        var1 = max(0.0, (sum_sq1 / n1) - (mean1 * mean1)) * (n1 / (n1 - 1.0))
        if var0 == 0.0 and var1 == 0.0:
            if abs(mean0 - mean1) > 1e-9:
                t_val = math.copysign(float("inf"), mean0 - mean1)
                return t_val, mean0, mean1, var0, var1
            return 0.0, mean0, mean1, var0, var1
        denom = math.sqrt((var0 / n0) + (var1 / n1))
        if denom < 1e-12:
            return 0.0, mean0, mean1, var0, var1
        return (mean0 - mean1) / denom, mean0, mean1, var0, var1

    def compute_statistic(self, key: Hashable) -> Optional[TVLAResult]:
        """Compute the Welch's t-test result for a scalar ``key``, or ``None`` if <2 samples."""
        acc = self._scalar_acc.get(key)
        if acc is None or acc[0] < 2.0 or acc[3] < 2.0:
            return None
        t_val, m0, m1, v0, v1 = self.welch_t(
            acc[0], acc[1], acc[2], acc[3], acc[4], acc[5]
        )
        return TVLAResult(
            key=key,
            t_stat=t_val,
            mean_fixed=m0,
            mean_random=m1,
            var_fixed=v0,
            var_random=v1,
            count_fixed=int(acc[0]),
            count_random=int(acc[3]),
        )

    def compute_vector_statistics(
        self, key: Hashable, nonzero_only: bool = False
    ) -> List[TVLAResult]:
        """Compute Welch's t-test results for all elements of vector ``key``."""
        vacc = self._vector_acc.get(key)
        if vacc is None or vacc.count[0] < 2 or vacc.count[1] < 2:
            return []
        n0 = float(vacc.count[0])
        n1 = float(vacc.count[1])
        s0_arr = vacc.sum[0]
        sq0_arr = vacc.sum_sq[0]
        s1_arr = vacc.sum[1]
        sq1_arr = vacc.sum_sq[1]
        results: List[TVLAResult] = []
        for idx in range(len(s0_arr)):
            t_val, m0, m1, v0, v1 = self.welch_t(
                n0, s0_arr[idx], sq0_arr[idx], n1, s1_arr[idx], sq1_arr[idx]
            )
            if nonzero_only and abs(t_val) == 0.0:
                continue
            elem_key: Any = (*key, idx) if isinstance(key, tuple) else (key, idx)
            results.append(
                TVLAResult(
                    key=elem_key,
                    t_stat=t_val,
                    mean_fixed=m0,
                    mean_random=m1,
                    var_fixed=v0,
                    var_random=v1,
                    count_fixed=vacc.count[0],
                    count_random=vacc.count[1],
                )
            )
        return results

    def compute_all(self, nonzero_only: bool = False) -> List[TVLAResult]:
        """Compute Welch's t-test results across all accumulated scalar and vector keys."""
        results: List[TVLAResult] = []
        for key, acc in self._scalar_acc.items():
            if acc[0] < 2.0 or acc[3] < 2.0:
                continue
            t_val, m0, m1, v0, v1 = self.welch_t(
                acc[0], acc[1], acc[2], acc[3], acc[4], acc[5]
            )
            if nonzero_only and abs(t_val) == 0.0:
                continue
            results.append(
                TVLAResult(
                    key=key,
                    t_stat=t_val,
                    mean_fixed=m0,
                    mean_random=m1,
                    var_fixed=v0,
                    var_random=v1,
                    count_fixed=int(acc[0]),
                    count_random=int(acc[3]),
                )
            )
        for vkey in self._vector_acc:
            results.extend(
                self.compute_vector_statistics(vkey, nonzero_only=nonzero_only)
            )
        return results

    def get_leaks(self, threshold: Optional[float] = None) -> List[TVLAResult]:
        """Return all results where ``|t_stat| > threshold``."""
        thresh = self.threshold if threshold is None else threshold
        return [
            res
            for res in self.compute_all(nonzero_only=True)
            if abs(res.t_stat) > thresh
        ]
