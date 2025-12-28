#!/usr/bin/python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Parse a yosys area report and give a kGE equivalient

import argparse
import re


def read_lib(lib_file_path, ref_cell):
    with open(lib_file_path, "r") as f:
        lib_file = f.readlines()

    cell_dict = {}
    weighted_dict = {}
    current_cell_name = None

    cell_pattern = re.compile(r'^\s*cell\s*\(\s*"?([a-zA-Z0-9_]+)"?\s*\)')
    area_pattern = re.compile(r"^\s*area\s*:\s*([0-9\.]+)\s*;")

    for line_idx, line in enumerate(lib_file):
        cell_match = cell_pattern.search(line)
        if cell_match:
            if current_cell_name is not None:
                pass
            current_cell_name = cell_match.group(1)
            continue

        area_match = area_pattern.search(line)
        if area_match and current_cell_name:
            try:
                cell_area = float(area_match.group(1))
                cell_dict[current_cell_name] = cell_area
                current_cell_name = None
            except ValueError:
                print(f"Warning: Could not parse area float at line {line_idx + 1}")

    if ref_cell not in cell_dict:
        raise RuntimeError(
            "Specified reference cell: {} was not found in library: {}".format(
                ref_cell, lib_file_path
            )
        )

    ref_area = cell_dict[ref_cell]
    if ref_area == 0:
        ref_area = 1.0

    for cell in cell_dict:
        weighted_dict[cell] = cell_dict[cell] / ref_area
    return weighted_dict


def get_kge(report_path, weighted_dict):
    try:
        with open(report_path, "r") as f:
            report = f.readlines()
    except FileNotFoundError:
        print(f"Error: Report file not found: {report_path}")
        return

    ge = 0.0
    for line in report:
        data = line.split()
        if len(data) < 2:
            continue

        name = None
        count = 0.0

        if data[0] in weighted_dict:
            name = data[0]
            try:
                count = float(data[1])
            except ValueError:
                continue
        elif data[1] in weighted_dict:
            name = data[1]
            try:
                count = float(data[0])
            except ValueError:
                continue

        if name:
            weight = weighted_dict[name]
            ge += count * weight

    print("Area in kGE = ", round(ge / 1000, 2))


def main():
    arg_parser = argparse.ArgumentParser(
        description="""Calculate kGE from a Yosys report and LIB file"""
    )

    arg_parser.add_argument("lib_file_path", help="Path to the LIB file")
    arg_parser.add_argument("report_path", help="Path to the report")
    arg_parser.add_argument(
        "--library", help="Reference library (default:nangate)", default="nangate"
    )

    args = arg_parser.parse_args()

    cell = None
    if args.library == "nangate":
        cell = "NAND2_X1"
    elif args.library == "sky130_fd_sc_hd":
        cell = "sky130_fd_sc_hd__nand2_1"
    else:
        raise RuntimeError("Library {} was not found".format(args.library))

    weighted_dict = read_lib(args.lib_file_path, cell)
    get_kge(args.report_path, weighted_dict)


if __name__ == "__main__":
    main()
