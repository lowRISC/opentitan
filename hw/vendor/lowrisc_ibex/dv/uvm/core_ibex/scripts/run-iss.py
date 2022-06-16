#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import os
import sys

from scripts_lib import get_config, get_isas_for_config, run_one


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--verbose', action='store_true')
    parser.add_argument('--iss', required=True)
    parser.add_argument('--input', required=True)
    parser.add_argument('--output', required=True)
    parser.add_argument('--ibex-config', required=True)

    args = parser.parse_args()

    cfg = get_config(args.ibex_config)
    isa, iss_isa = get_isas_for_config(cfg)

    # riscv-dv knows how to run an ISS simulation (see yaml/iss.yaml in the
    # vendored directory), but it has definite (and inconvenient!) opinions
    # about where files should end up. Rather than fight with it, let's just
    # generate the simple ISS command ourselves.
    #
    # NOTE: This only supports Spike, mainly because it's the only simulator we
    # care about at the moment and this whole script is going to go away anyway
    # very soon once we've switched across to using cosimulation.

    if args.iss != 'spike':
        raise RuntimeError(f'Unsupported ISS: {args.iss}')

    spike_dir = os.getenv('SPIKE_PATH')
    if spike_dir is not None:
        spike = os.path.join(spike_dir, 'spike')
    else:
        spike = 'spike'

    cmd = [spike, '--log-commits', '--isa', iss_isa, '-l', args.input]
    return run_one(args.verbose,
                   cmd,
                   redirect_stdstreams=args.output,
                   timeout_s=30)  # Spike can run indefinitely in some cases


if __name__ == '__main__':
    sys.exit(main())
