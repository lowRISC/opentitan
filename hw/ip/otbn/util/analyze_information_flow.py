#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import sys

from shared.constants import parse_required_constants
from shared.control_flow import program_control_graph, subroutine_control_graph
from shared.decode import decode_elf
from shared.information_flow import InformationFlowGraph
from shared.information_flow_analysis import (get_program_iflow,
                                              get_subroutine_iflow,
                                              stringify_control_deps)


def main() -> int:
    parser = argparse.ArgumentParser(description=(
        'Analyze the control flow and information flow of an OTBN '
        'program or subroutine.'))
    parser.add_argument('elf', help=('The .elf file to check.'))
    parser.add_argument(
        '--verbose',
        action='store_true',
        help=('Print full control-flow and information-flow graphs.'))
    parser.add_argument(
        '--subroutine',
        required=False,
        help=(
            'The specific subroutine to check. If not provided, start point is '
            '_imem_start (whole program).'))
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
        help=(
            'Initially secret information-flow nodes. If provided, the final '
            'secrets will be printed.'))
    args = parser.parse_args()
    program = decode_elf(args.elf)

    # Compute control-flow graph.
    if args.subroutine is None:
        graph = program_control_graph(program)
    else:
        graph = subroutine_control_graph(program, args.subroutine)

    # Only print the control-flow graph if --verbose is set.
    if args.verbose:
        print('Control-flow graph:')
        print(graph.pretty(program, indent=2))
        cycle_pcs = graph.get_cycle_starts()
        if cycle_pcs:
            print('Control flow has cycles starting at the following PCs:')
            for pc in cycle_pcs:
                symbols = program.get_symbols_for_pc(pc)
                label_str = ' <{}>'.format(
                    ', '.join(symbols)) if symbols else ''
                print('{:#x}{}'.format(pc, label_str))

    # Parse initial constants.
    if args.constants is None:
        constants = {}
    else:
        if args.subroutine is None:
            raise ValueError('Cannot require initial constants for a whole '
                             'program; use --subroutine to analyze a specific '
                             'subroutine.')
        constants = parse_required_constants(args.constants)

    # Compute information-flow graph(s).
    if args.subroutine is None:
        what = 'program'
        end_iflow, control_deps = get_program_iflow(program, graph)
        ret_iflow = InformationFlowGraph.nonexistent()
    else:
        what = 'subroutine'
        ret_iflow, end_iflow, control_deps = get_subroutine_iflow(
            program, graph, args.subroutine, constants)

    # If no secrets were given or the --verbose flag is set, then print the
    # full information-flow graphs.
    if (args.verbose or args.secrets is None):
        if ret_iflow.exists:
            print(
                'Information flow for paths ending in a return to the caller:')
            print(ret_iflow.pretty(indent=2))
            if end_iflow.exists:
                print('--------')

        if end_iflow.exists:
            print('Information flow for paths ending the program:')
            print(end_iflow.pretty(indent=2))

    if args.secrets is None:
        # If no initial secrets were provided, we will print all nodes that
        # could influence control flow.
        control_what = 'information-flow nodes'
    else:
        # If secrets were provided, only show the ways in which those specific
        # nodes could influence control flow.
        control_what = 'secrets'
        control_deps = {
            name: pcs
            for name, pcs in control_deps.items() if name in args.secrets
        }

    # Print any (secret) nodes that influence control flow, and the PCs of the
    # control-flow instructions they influence.
    if len(control_deps) == 0:
        print('No {} were found to influence this {}\'s control flow.'.format(
            control_what, what))
    else:
        print('The following {} may influence control flow in this {}:'.format(
            control_what, what))
        for node in stringify_control_deps(program, control_deps):
            print(node)

    # Print final secrets (if initial secrets were provided).
    if args.secrets is not None:
        if ret_iflow.exists:
            final_secrets = {
                sink
                for node in args.secrets for sink in ret_iflow.sinks(node)
            }
            print('Final secrets for paths ending in a return to the caller:',
                  ', '.join(sorted(final_secrets)))
        if end_iflow.exists:
            final_secrets = {
                sink
                for node in args.secrets for sink in end_iflow.sinks(node)
            }
            print('Final secrets for paths ending the program:',
                  ', '.join(sorted(final_secrets)))

    return 0


if __name__ == "__main__":
    sys.exit(main())
