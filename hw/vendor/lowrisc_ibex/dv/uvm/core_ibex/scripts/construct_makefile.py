#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import sys


def transform(discard_stdstreams: bool,
              cmdlist_path: str,
              makefile_path: str) -> None:
    '''Transform a list of commands to a Makefile'''
    # Many commands come with a logfile argument, however some capture the
    # stdout/stderr to a file. Handle both cases to ensure the logs are tidy.
    tail = '\n'
    if discard_stdstreams:
        tail = ' >/dev/null 2>&1' + tail

    with open(cmdlist_path) as f, \
         open(makefile_path, 'w', encoding='UTF-8') as outfile:
        ctr = 0
        for line in f:
            line = line.strip()
            if not line:
                continue

            outfile.write(f'{ctr}:\n')
            outfile.write('\t' + line.strip() + tail)
            ctr += 1

        outfile.write(f'CMDS := $(shell seq 0 {ctr - 1})\n')
        outfile.write('all: $(CMDS)')


def main() -> int:
    """
    Construct a trivial makefile from the --debug output of riscv-dv commands.

    Creates a flat makefile, so if the commands have any ordering requirements
    this will fall over.
    """
    parser = argparse.ArgumentParser()
    parser.add_argument('--test_cmds', required=True,
                        help='File containing --debug output')
    parser.add_argument('--output', required=True,
                        help='Makefile to be constructed')
    parser.add_argument("--discard_stdstreams", action='store_true',
                        help='Redirect stdstreams to /dev/null')
    args = parser.parse_args()

    transform(args.discard_stdstreams, args.test_cmds, args.output)
    return 0


if __name__ == '__main__':
    sys.exit(main())
