#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Sparse state machine encoding generator

"""

import argparse


def check_hamming(enc, enc_list, hdist):
    for i in enc_list:
        bit_diff = bin(i ^ enc).count("1")
        if bit_diff < hdist:
            return 0
    return 1


def main():
    parser = argparse.ArgumentParser(
        prog="sparse_state_gen",
        description='''This tool generates encodings for sparsely populated
        state machines in SystemVerilog.
        '''
    )
    parser.add_argument(
        '--dist', nargs=1, dest='hdist', default=3,
        help='Specify the minimum hamming distance, default:3')
    parser.add_argument('states', nargs='+', help='List the names of all states')

    args = parser.parse_args()

    # Get the number of defined states
    num_states = len(args.states)

    # Generate the required encodings, starting from 0
    current_encoding = 0
    encodings_list = []
    while len(encodings_list) < num_states:
        while check_hamming(current_encoding, encodings_list, args.hdist) == 0:
            current_encoding += 1
        encodings_list.append(current_encoding)

    # How many bits to represent the state
    states_width = int.bit_length(encodings_list[-1])

    # Calculate longest state name (for tabular alignment)
    max_label_len = len(max(args.states, key=len))

    # Construct the typedef template with comments
    typedef_string = '  // States encoded to have hamming distance >= %d' % args.hdist
    typedef_string += ' between valid states\n'
    typedef_string += '  // NOTE: ensure synthesis tool does not re-encode states for'
    typedef_string += ' this to be useful\n'
    typedef_string += '  typedef enum logic [%d:0] {\n' % (states_width - 1)
    index = 0
    for i in args.states:
        typedef_string += '    ' + i
        typedef_string += (max_label_len - len(i)) * ' '
        typedef_string += ' = ' + str(states_width) + '\'b'
        typedef_string += format(encodings_list[index], '0%db' % states_width)
        if index < (len(args.states) - 1):
            typedef_string += ',\n'
        else:
            typedef_string += '\n'
        index += 1
    typedef_string += '  } state_name_e;'

    print(typedef_string)


if __name__ == "__main__":
    main()
