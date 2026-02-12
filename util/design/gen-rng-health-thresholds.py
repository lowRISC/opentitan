#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""This script generates health threshold configuration values for the
entropy_src block.

The implementation is identical to the `ideal_threshold_recommendation` DV
utility function available in dv/env/entropy_src_env_pkg.sv.



The sigma value versus probability of test failure is as follows (taken from
the reference above):

No. of sigma  | Approximate probability of test failure ( P(x) = 1 - erf( x / sqrt(2) ))
--------------|----------------------------------
            1 |  31.7%
          1.5 |  13.4%
            2 |   4.6%
          2.5 |   1.2%
            3 |  0.27%
          3.3 |   0.1%
          3.9 |   1e-4
         4.42 |   1e-5
          4.9 |   1e-6

Notes:

`--window_size` must be set to reflect the respective `FIPS_WINDOW` or
`BYPASS_WINDOW` in bits. The following are window size recommended values:

- FIPS: 2048
- Boot mode: 384

`--per-line` must be set to reflect the `THRESHOLD_SCOPE` ENTROPY_SRC configuration.

- 0: `THRESHOLD_SCOPE` = True
- 1: `THRESHOLD_SCOPE` = False

`--rng_bit_enable` must be set to reflect the `RNG_BIT_ENABLE` ENTROPY_SRC configuration.

"""
import argparse
import enum
import math
import sys

# Matches the `BucketHtDataMaxWidth` in entropy_src_pkg.sv
_BUCKET_HT_DATA_MAX_WIDTH = 4


# List of test windows supported by this script.
class _Test(enum.Enum):
    ADAPTP = 'ADAPTP'
    BUCKET = 'BUCKET'
    MARKOV = 'MARKOV'


def threshold_calc(test: str, window_size: int, rng_bus_width: int,
                   per_line: bool, rng_bit_enable: bool, sigma: float) -> bool:
    """Calculates and prints high and low entropy health test thresholds.

    Args:
        test: Test name.
        window_size: Window size in bits.
        rng_bus_width: Symbol size in bits.
        per_line: Set to true to score adaptive proportion and Markov tests on
        a per-line basis
        rng_bit_enable: Set to true to make calculations assuming single bit
        entropy.
        sigma: Number of standard deviations to provide between the range. This
        assumes that the window is large enough to treat the test as normally
        distributed.
    Returns:
        False if unable to calculate the thresholds. True otherwise.
    """

    bucket_ht_data_width: int = _BUCKET_HT_DATA_MAX_WIDTH if rng_bus_width \
        >= _BUCKET_HT_DATA_MAX_WIDTH else rng_bus_width
    num_buckets: int = 2**bucket_ht_data_width
    num_bucket_ht_inst: int = -(rng_bus_width // -bucket_ht_data_width)

    n: int = 0
    p: float = 0.5

    if test == _Test.ADAPTP:
        n = window_size if (not per_line or
                            rng_bit_enable) else window_size / rng_bus_width
    elif test == _Test.BUCKET:
        n = window_size / bucket_ht_data_width / num_bucket_ht_inst
        p = 1.0 / float(num_buckets)
    elif test == _Test.MARKOV:
        half_window = window_size / 2
        n = half_window if (not per_line or
                            rng_bit_enable) else half_window / rng_bus_width
    else:
        print(f"Invalid test name {test}")
        return False

    mean = p * n
    stddev = math.sqrt(p * (1 - p) * n)

    low = 0 if test == _Test.BUCKET else math.floor(mean - sigma * stddev)
    high = math.ceil(mean + sigma * stddev)

    # For large values of sigman, the gaussian approximation can recommend
    # thresholds larger than the total number of trials. In such cases, we
    # cap the threshold at the total number of trials for the given test.
    low = 0 if low < 0 else low
    high = n if high > n else high

    print(f"{test.value}_HI: 0x{int(high):08x} {int(high):0d}")
    print(f"{test.value}_LO: 0x{int(low):08x} {int(low):0d}")

    return True


def main():
    parser = argparse.ArgumentParser(
        prog="gen-rng-health-thresholds",
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--window_size',
                        '-w',
                        type=int,
                        default=2048,
                        help='Window size in bits.')
    parser.add_argument('--rng_bus_width',
                        '-r',
                        type=int,
                        default=4,
                        help='Symbol size in bits.')
    parser.add_argument('--per_line',
                        '-l',
                        action='store_true',
                        default=False,
                        help='''
                        Set to true to score adaptive proportion and Markov
                        tests on a per-line basis.
                        ''')
    parser.add_argument('--rng_bit_enable',
                        '-b',
                        action='store_true',
                        default=False,
                        help='''
                        Set to true to make calculations assuming single bit
                        entropy.
                        ''')
    parser.add_argument('--sigma',
                        '-s',
                        type=float,
                        default=3.0,
                        help='''
                        Number of standard deviations to support in the test
                        window threshold.
                        ''')
    args = parser.parse_args()

    print(
        f"Window size: {args.window_size:d}, RNG bus width: {args.rng_bus_width:d}, "
        +
        f"per_line: {args.per_line}, rng_bit_enable: {args.rng_bit_enable}, " +
        f"sigma: {args.sigma:0.2f}")
    results = [
        threshold_calc(t, args.window_size, args.rng_bus_width, args.per_line,
                       args.rng_bit_enable, args.sigma) for t in _Test
    ]
    if not all(results):
        sys.exit("Failed to calculate one or more thresholds.")


if __name__ == "__main__":
    main()
