#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This script reads three files [1], [2], [3] and constructs file [4], such that:
# [1] Original techlib verilog file
# [2] Manually written patch file that contains new cell definitions
# [3] The synthesized netlist file (consisting of techlib cells)
# [4] The techlib file created by this script that contains cell definitions only for cells used
# in the netlist.
# Hence, for all cells from [3], obtain definitions from [1] and [2] and write it to [4].

import re
import os

# Paths for the files [1], [2], [3], [4] respectively:
techlib_file_name = os.environ["SIM_MODEL_FILE"]
patch_file_name = os.environ["SIM_PATCH_FILE"]
netlist_file_name = os.environ["AES_SBOX_NETLIST_FILE"]
modified_techlib_file_name = os.environ["MODIFIED_TECHLIB_FILE"]


# Parse all techlib cell names from a given file and return a dictionary (by using a specific
# regexp), where dictionary keys are cell names and items are cell counts.
def get_cell_list_from_file(filename):
    cell_pattern = re.compile("SEN_(\\S)+")
    all_cells = {}
    for line_nr, line in enumerate(open(filename, "r")):
        match_obj = re.search(cell_pattern, line)
        if match_obj is not None:
            cell_name = match_obj.group(0)
            if cell_name in all_cells:
                all_cells[cell_name] += 1
            else:
                all_cells[cell_name] = 1
        all_cells = dict(sorted(all_cells.items()))
    return all_cells


# Given a string that contains both the cell name and its verilog definiton, simply return the name
# as string.
def get_cell_name(cell_def_str):
    cell_name = re.findall("SEN_\\w*", cell_def_str)
    # Drop multiple occurences of the same cell labels
    return cell_name[0]


# Then create a dictionary of cells where keys are cell names and items are their multi-line verilog
# description as strings.
# As we are processing cells at a time, remove parts the definition that Yosys does not like
# (e.g. specify blocks, celldefine macros etc.)
def get_cell_dict(techlib_verilog_str):
    # Remove timing blocks, as read_verilog of Yosys cannot digest them
    file_content = re.sub("specify.*?endspecify",
                          "\\t\\t// specify block removed", techlib_verilog_str, flags=re.DOTALL)
    # Make non-greedy search so that each cell is another match
    cell_defs = re.findall("`celldefine.*?`endcelldefine", file_content, re.DOTALL)
    cell_def_dict = {}
    for cell in cell_defs:
        cell = cell.replace("`celldefine", "")
        cell = cell.replace("`endcelldefine", "")
        cell_name = get_cell_name(cell)
        cell_def_dict[cell_name] = cell
    return cell_def_dict


# Replace the name of the cell with given new cell.
def rename_cell_def(cell_def, old_cell_name, new_cell_name):
    cell_def = cell_def.replace(old_cell_name, new_cell_name)
    cell_def = "// patched by " + old_cell_name + "\n" + cell_def
    print(new_cell_name, " is patched by", old_cell_name)
    return cell_def


# There are generally cells with different sizes that look like:
# ABC_NANDGATE_1, ABC_NANDGATE_2, ABC_NANDGATE_3 etc.
# Here, if we need to patch this cell, we would provide a template cell with name `ABC_NANDGATE_`
# so that it can be reused for all sizes of the same type cells.
# This function checks if given `full_cell_name` matches `template_cell_name` (which is simple
# check of substring).
def is_cell_patched(template_cell_name, full_cell_name):
    str_pos = full_cell_name.find(template_cell_name)
    return str_pos == 0


if __name__ == "__main__":
    # Read all cell names used by the netlist
    include_dict = get_cell_list_from_file(netlist_file_name)

    print("The following cells are used in the given S-box netlist:")
    print("<count>\t\t<cell_name>")
    for key, val in include_dict.items():
        print(val, key, sep="\t\t")

    techlib_str = open(techlib_file_name, "r").read()
    patchlib_str = open(patch_file_name, "r").read()
    modified_techlib_file_name = open(modified_techlib_file_name, "w")

    techlib_cell_dict = get_cell_dict(techlib_str)
    patchlib_cell_dict = get_cell_dict(patchlib_str)

    for (cell_name, cell_def) in techlib_cell_dict.items():
        if cell_name not in include_dict.keys():
            continue
        # Check if we need to patch `cell_name`
        for (template_cell_name, template_cell_def) in patchlib_cell_dict.items():
            if is_cell_patched(template_cell_name, cell_name):
                cell_def = rename_cell_def(template_cell_def, template_cell_name, cell_name)

        modified_techlib_file_name.write(cell_def)

    modified_techlib_file_name.close()
