#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""FuseSoc generator for UVM RAL package created with either regtool or
topgen tools.
"""
import os
import subprocess
import sys

import yaml

try:
    from yaml import CSafeLoader as YamlLoader
except ImportError:
    from yaml import SafeLoader as YamlLoader

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
    dv_base_prefix = gapi['parameters'].get('dv_base_prefix')
    if not name or (bool(ip_hjson) == bool(top_hjson)):
        print("Error: ralgen requires the \"name\" and exactly one of "
              "{\"ip_hjson\" and \"top_hjson\"} parameters to be set.")
        sys.exit(1)

    # Generate the RAL pkg.
    if ip_hjson:
        ral_spec = get_full_path(root_dir, ip_hjson)
        cmd = os.path.join(util_path, "regtool.py")
        args = [cmd, "-s", "-t", ".", ral_spec]
    else:
        ral_spec = get_full_path(root_dir, top_hjson)
        cmd = os.path.join(util_path, "topgen.py")
        args = [cmd, "-r", "-o", ".", "-t", ral_spec]

    if dv_base_prefix and dv_base_prefix != "dv_base":
        args.extend(["--dv-base-prefix", dv_base_prefix])

    try:
        subprocess.run(args, check=True)
    except subprocess.CalledProcessError as e:
        print("Error: RAL pkg generation failed:\n{}".format(str(e)))
        sys.exit(e.returncode)
    print("RAL pkg for {} block written to {}"
          .format(name, os.path.abspath('.')))


if __name__ == '__main__':
    main()
