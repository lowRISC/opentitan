# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import csv
import os
import re
import sys

ys_translate_script_filename = 'translate_names.ys'
ys_translated_names = 'ys_translated_names'
generated_cell_re = re.compile(r'(_\w+_)/(\w+)')
ys_tcl = './tcl/yosys_post_synth.tcl'


def create_translate_names_script(cells_to_translate, top_level, gen_out):
    yosys_script_file = open(
        '{}/{}'.format(gen_out, ys_translate_script_filename), 'w')

    yosys_script_file.write('tcl {}\n'.format(ys_tcl))
    yosys_script_file.write('cd {}\n'.format(top_level))

    for cell in cells_to_translate:
        yosys_script_file.write('select {} %x:+[Q]\n'.format(cell))
        yosys_script_file.write('tee -a {}/{} select -list\n'.format(
            gen_out, ys_translated_names))

    yosys_script_file.close()


def extract_path_info(timing_csv):
    timing_in = csv.reader(open(timing_csv))

    cells_to_translate = set()
    path_info = []

    for line in timing_in:
        points = []

        for i in range(2):
            cell_match = generated_cell_re.search(line[i])
            if cell_match:
                cells_to_translate.add(cell_match.group(1))
                points.append(cell_match.group(1))
            else:
                points.append(line[i])

        path_info.append((points[0], points[1], float(line[2])))

    return (cells_to_translate, path_info)


def build_translated_names_dict(translated_names_file):
    translated_names = open(translated_names_file)
    translated_name_lines = translated_names.readlines()

    translated_names_dict = {}

    for i in range(0, len(translated_name_lines), 2):
        translated_name = translated_name_lines[i][:-1].split('/', 1)[1]
        cell_name = translated_name_lines[i + 1][:-1].split('/', 1)[1]

        translated_names_dict[cell_name] = translated_name

    return translated_names_dict


def translate_path_info(path_info, translated_names_file):
    translated_names_dict = build_translated_names_dict(translated_names_file)

    new_path_info = []

    for path in path_info:
        translated_path = list(path)
        points = path[0:1]
        for i in range(2):
            if path[i] in translated_names_dict:
                translated_path[i] = translated_names_dict[path[i]]

        new_path_info.append(tuple(translated_path))

    return new_path_info
