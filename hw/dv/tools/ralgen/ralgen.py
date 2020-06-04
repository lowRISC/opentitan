#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""FuseSoc generator for UVM RAL package created with either regtool or
topgen tools.
"""
import argparse
import os
import subprocess
import sys

import yaml

try:
    from yaml import CSafeLoader as YamlLoader, CSafeDumper as YamlDumper
except ImportError:
    from yaml import SafeLoader as YamlLoader, SafeDumper as YamlDumper

# Repo root is 4 levels up. Note that this will require an update if the path to
# this tool is changed.
REPO_ROOT = "../../../.."


# Given a root dir and partial path, this function returns the full path.
def get_full_path(root_dir, partial_path):
    full_path = os.path.abspath(os.path.join(root_dir, partial_path))
    if not os.path.exists(full_path):
        print("Error: path appears to be invalid: {}".format(full_path))
        sys.exit(1)
    return full_path


def main():
    if len(sys.argv) != 2:
        print("ERROR: This script takes a single YAML file as input argument")
        sys.exit(1)

    gapi_filepath = sys.argv[1]
    gapi = yaml.load(open(gapi_filepath), Loader=YamlLoader)

    # This is just a wrapper around the reggen and topgen tools, which
    # are referenced from proj_root area.
    self_path = os.path.dirname(os.path.realpath(__file__))
    util_path = os.path.abspath(os.path.join(self_path, REPO_ROOT, "util"))

    # Retrieve the parameters from the yml.
    root_dir = gapi['files_root']
    name = gapi['parameters'].get('name')
    ip_hjson = gapi['parameters'].get('ip_hjson')
    top_hjson = gapi['parameters'].get('top_hjson')
    if not name or (bool(ip_hjson) == bool(top_hjson)):
        print("Error: ralgen requires the \"name\" and exactly one of "
              "{\"ip_hjson\" and \"top_hjson\"} parameters to be set.")
        sys.exit(1)

    # Generate the RAL pkg.
    ral_pkg_file = name + "_ral_pkg.sv"
    if ip_hjson:
        ral_spec = get_full_path(root_dir, ip_hjson)
        cmd = os.path.join(util_path, "regtool.py")
        args = [cmd, "-s", "-t", ".", ral_spec]
    else:
        ral_spec = get_full_path(root_dir, top_hjson)
        cmd = os.path.join(util_path, "topgen.py")
        args = [cmd, "-r", "-o", ".", "-t", ral_spec]

    try:
        subprocess.run(args, check=True)
    except subprocess.CalledProcessError as e:
        print("Error: RAL pkg generation failed:\n{}".format(str(e)))
        sys.exit(e.returncode)
    print("RAL pkg file written to {}".format(os.path.abspath(ral_pkg_file)))

    # Generate the FuseSoc core file.
    ral_pkg_core_text = {
        'name': "lowrisc:dv:{}_ral_pkg".format(name),
        'filesets': {
            'files_dv': {
                'depend': [
                    "lowrisc:dv:dv_base_reg",
                ],
                'files': [
                    ral_pkg_file,
                ],
                'file_type': 'systemVerilogSource'
            },
        },
        'targets': {
            'default': {
                'filesets': [
                    'files_dv',
                ],
            },
        },
    }
    ral_pkg_core_file = os.path.abspath(name + "_ral_pkg.core")
    with open(ral_pkg_core_file, 'w') as f:
        f.write("CAPI=2:\n")
        yaml.dump(ral_pkg_core_text,
                  f,
                  encoding="utf-8",
                  default_flow_style=False,
                  sort_keys=False)
    print("RAL core file written to {}".format(ral_pkg_core_file))


if __name__ == '__main__':
    main()
