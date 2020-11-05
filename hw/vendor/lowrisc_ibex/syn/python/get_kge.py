#!/usr/bin/python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Parse a yosys area report and give a kGE equivalient

import argparse


def read_lib(lib_file_path, ref_cell):
    with open(lib_file_path, 'r') as f:
        lib_file = f.readlines()

    cell_dict = {}
    weighted_dict = {}
    cell_name = None
    for line_idx, line in enumerate(lib_file):
        if line.startswith('  cell ('):
            if cell_name is not None:
                raise RuntimeError('{}:{} Found cell while searching for area'
                                   .format(lib_file_path, line_idx + 1))
            cell_name = line.split()[1].strip('()')
        elif line.startswith('\tarea'):
            if cell_name is None:
                raise RuntimeError('{}:{} Found area while searching for cell'
                                   .format(lib_file_path, line_idx + 1))
            try:
                cell_area = line.split()[2].strip(';')
                cell_dict[cell_name] = float(cell_area)
                cell_name = None
            except (IndexError, ValueError):
                raise RuntimeError('{}:{} Area declaration misformatted'
                                   .format(lib_file_path, line_idx + 1))

    if ref_cell not in cell_dict:
        raise RuntimeError('Specified reference cell: {} was not found in '
                           'library: {}' .format(ref_cell, lib_file_path))

    for cell in cell_dict:
        weighted_dict[cell] = cell_dict[cell] / cell_dict[ref_cell]
    return weighted_dict


def get_kge(report_path, weighted_dict):
    with open(report_path, 'r') as f:
        report = f.readlines()
    ge = 0.0
    for line_idx, line in enumerate(report):
        data = line.split()
        if not data:
            continue
        weight = weighted_dict.get(data[0])
        if weight is not None:
            try:
                ge += float(data[1]) * weight
            except (IndexError, ValueError):
                raise RuntimeError('{}:{} Cell {} matched but was misformatted'
                                   .format(report_path, line_idx + 1, data[0]))
    print("Area in kGE = ", round(ge/1000, 2))


def main():
    arg_parser = argparse.ArgumentParser(
        description="""Calculate kGE from a Yosys report and LIB file""")

    arg_parser.add_argument('lib_file_path', help='Path to the LIB file')
    arg_parser.add_argument('report_path', help='Path to the report')
    arg_parser.add_argument('--cell', help='Reference cell (default:NAND2_X1)',
                            default='NAND2_X1')

    args = arg_parser.parse_args()

    weighted_dict = read_lib(args.lib_file_path, args.cell)
    get_kge(args.report_path, weighted_dict)


if __name__ == "__main__":
    main()
