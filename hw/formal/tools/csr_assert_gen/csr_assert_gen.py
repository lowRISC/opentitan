#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""FuseSoc generator for creating the CSR assert file using regtool.py, used
in DV and FPV testbenches.
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


def main():
    if len(sys.argv) != 2:
        print("ERROR: This script takes a single YAML file as input argument")
        sys.exit(1)

    gapi_filepath = sys.argv[1]
    gapi = yaml.load(open(gapi_filepath), Loader=YamlLoader)

    # This is just a wrapper around regtool.py from proj_root/util area.
    self_path = os.path.dirname(os.path.realpath(__file__))
    util_path = os.path.abspath(os.path.join(self_path, REPO_ROOT, "util"))

    # Retrieve the parameters from the yml.
    files_root_dir = gapi['files_root']
    spec = gapi['parameters'].get('spec')

    if not spec:
        print("Error: \"spec\" parameter missing or invalid: {}".format(spec))
        sys.exit(1)

    # Convert spec (partial path relative to `files_root_dir`) into absolute
    # path so that we can pass it to `regtool.py`.
    spec = os.path.abspath(os.path.join(files_root_dir, spec))
    if not os.path.exists(spec):
        print("Error: spec path appears to be invalid: {}".format(spec))
        sys.exit(1)

    cmd = os.path.join(util_path, "regtool.py")
    args = [cmd, "-f", "-t", ".", spec]

    try:
        subprocess.run(args, check=True)
    except subprocess.CalledProcessError as e:
        print("Error: CSR assert gen failed:\n{}".format(str(e)))
        sys.exit(e.returncode)


if __name__ == '__main__':
    main()
