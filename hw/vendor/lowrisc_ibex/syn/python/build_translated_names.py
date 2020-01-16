#!/usr/bin/python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import subprocess

from flow_utils import *


def main():
    arg_parser = argparse.ArgumentParser(
        description=
        """Uses yosys to translate cell names from given timing reports to human
        readable names (assumes flatted synthesis run)""")

    arg_parser.add_argument('top_level', help='Name of the top-level module')
    arg_parser.add_argument(
        'gen_out', help='Path to place generated script and script output')
    arg_parser.add_argument(
        'rpts',
        nargs='+',
        help='Report files to generate human readable names from')

    args = arg_parser.parse_args()

    cells_to_translate = set()

    for csv_rpt in args.rpts:
        (new_cells_to_translate, path_info) = extract_path_info(csv_rpt)
        cells_to_translate.update(new_cells_to_translate)

    create_translate_names_script(cells_to_translate, args.top_level,
                                  args.gen_out)

    yosys_cmd = [
        'yosys', '-s', '{}/{}'.format(args.gen_out,
                                      ys_translate_script_filename)
    ]

    subprocess.run(yosys_cmd)


if __name__ == "__main__":
    main()
