#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import sys

from shared.check import CheckResult
from shared.constants import parse_required_constants
from shared.control_flow import program_control_graph, subroutine_control_graph
from shared.decode import decode_elf
from shared.information_flow_analysis import (get_program_iflow,
                                              get_subroutine_iflow,
                                              stringify_control_deps)


def main() -> int:
    parser = argparse.ArgumentParser(
        description='Analyze whether secret data affects the control flow of '
        'an OTBN program or subroutine.')
    parser.add_argument('elf', help=('The .elf file to check.'))
    parser.add_argument('--verbose', action='store_true')
    parser.add_argument(
        '--subroutine',
        required=False,
        help=('The specific subroutine to check. If not provided, the start '
              'point is _imem_start (whole program).'))
    parser.add_argument(
        '--constants',
        nargs='+',
        type=str,
        required=False,
        help=('Registers which are required to be constant at the start of the '
              'subroutine. Only valid if `--subroutine` is passed. Write '
              'in the form "reg:value", e.g. x3:5. Only GPRs are accepted as '
              'required constants.'))
    parser.add_argument(
        '--secrets',
        nargs='+',
        type=str,
        required=False,
        help=('Initial secret information-flow nodes. If not provided, '
              'assume everything is secret; check that the subroutine or '
              'program has only one possible control-flow path regardless '
              'of input.'))
    args = parser.parse_args()

    # Parse initial constants.
    if args.constants is None:
        constants = {}
    else:
        if args.subroutine is None:
            raise ValueError('Cannot require initial constants for a whole '
                             'program; use --subroutine to analyze a specific '
                             'subroutine.')
        constants = parse_required_constants(args.constants)

    # Compute control graph and get all nodes that influence control flow.
    program = decode_elf(args.elf)
    if args.subroutine is None:
        graph = program_control_graph(program)
        to_analyze = 'entire program'
        _, control_deps = get_program_iflow(program, graph)
    else:
        graph = subroutine_control_graph(program, args.subroutine)
        to_analyze = 'subroutine {}'.format(args.subroutine)
        _, _, control_deps = get_subroutine_iflow(program, graph,
                                                  args.subroutine, constants)

    if args.secrets is None:
        if args.verbose:
            print(
                'No specific secrets provided; checking that {} has only one '
                'control-flow path'.format(to_analyze))
        secret_control_deps = control_deps
    else:
        if args.verbose:
            print('Analyzing {} with initial secrets {} and initial constants {}'.format(
                to_analyze, args.secrets, constants))
        # If secrets were provided, only show the ways in which those specific
        # nodes could influence control flow.
        secret_control_deps = {
            node: pcs
            for node, pcs in control_deps.items() if node in args.secrets
        }

    out = CheckResult()

    if len(secret_control_deps) != 0:
        msg = 'The following secrets may influence control flow:\n  '
        msg += '\n  '.join(stringify_control_deps(program,
                                                  secret_control_deps))
        out.err(msg)

    if args.verbose or out.has_errors() or out.has_warnings():
        print(out.report())

    if out.has_errors() or out.has_warnings():
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main())
