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
    name = os.path.basename(spec).replace(".hjson", "")
    depend = gapi['parameters'].get('depend') or "lowrisc:ip:{}".format(name)

    if not name or not spec:
        print("Error: \"spec\" parameter missing or invalid: {}".format(spec))
        sys.exit(1)

    # Generate the CSR assert file.
    csr_assert_file = name + "_csr_assert_fpv.sv"

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
    print("CSR assert file written to {}".format(
        os.path.abspath(csr_assert_file)))

    # Generate the FuseSoc core file.
    csr_assert_core_text = {
        'name': "lowrisc:fpv:{}_csr_assert".format(name),
        'filesets': {
            'files_dv': {
                'depend': [
                    depend,
                    "lowrisc:tlul:headers",
                    "lowrisc:prim:assert",
                ],
                'files': [
                    csr_assert_file,
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
    csr_assert_core_file = os.path.abspath(name + "_csr_assert_fpv.core")
    with open(csr_assert_core_file, 'w') as f:
        f.write("CAPI=2:\n")
        yaml.dump(csr_assert_core_text,
                  f,
                  encoding="utf-8")
    print("CSR assert core file written to {}".format(csr_assert_core_file))


if __name__ == '__main__':
    main()
