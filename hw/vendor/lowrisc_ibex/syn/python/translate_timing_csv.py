#!/usr/bin/python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse

from flow_utils import *


def main():
    arg_parser = argparse.ArgumentParser(
        description=
        """Translates CSV timing report to have human readable start and end
        points given yosys generated name translation file (generated with
        build_translated_names.py""")

    arg_parser.add_argument('rpt_file', help='Name of the CSV report file')
    arg_parser.add_argument(
        'gen_out', help='Path containing generated name translation file')

    args = arg_parser.parse_args()

    (cells_to_translate, path_info) = extract_path_info(args.rpt_file)

    path_info = translate_path_info(
        path_info, '{}/{}'.format(args.gen_out, ys_translated_names))

    translated_rpt_out = open(sys.argv[1], 'w')

    translated_rpt_out.write('Start Point, End Point, WNS (ns)\n')

    for p in path_info:
        translated_rpt_out.write('{},{},{}\n'.format(p[0], p[1], p[2]))

    translated_rpt_out.close()


if __name__ == "__main__":
    main()
