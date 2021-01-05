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
import logging as log
from shutil import copyfile
from collections import OrderedDict
import pathlib

import yaml

try:
    from yaml import CSafeLoader as YamlLoader, CSafeDumper as YamlDumper
except ImportError:
    from yaml import SafeLoader as YamlLoader, SafeDumper as YamlDumper

# RSTMGR root
RSTMGR_ROOT = "/../"


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

    if 'verbose' in gapi['parameters']:
        if gapi['parameters'].get('verbose') == 1:
            log.basicConfig(format="%(levelname)s: %(message)s", level=log.DEBUG)
        else:
            log.basicConfig(format="%(levelname)s: %(message)s")

    # Retrieve the parameters from the yml.
    if 'path' not in gapi['parameters']:
        log.error("path to RTL not supplied")
        sys.exit(1)
    else:
        rtl_path = self_path + RSTMGR_ROOT + gapi['parameters']['path']
        print("RTL path %s" % (rtl_path, ))

    # Retrieve the command from the yml.
    cmd = ""
    if 'cmd' not in gapi['parameters']:
        log.error("command not given")
        sys.exit(1)
    else:
        cmd = gapi['parameters']['cmd']


    # Copy generated rtl files
    copyfile(rtl_path + "/rstmgr_pkg.sv", "rstmgr_pkg.sv")
    copyfile(rtl_path + "/rstmgr_reg_pkg.sv", "rstmgr_reg_pkg.sv")
    copyfile(rtl_path + "/rstmgr_reg_top.sv", "rstmgr_reg_top.sv")

    # Copy common rtl files
    common_path = self_path + RSTMGR_ROOT + "rtl"
    copyfile(rtl_path + "/rstmgr_ctrl.sv", "rstmgr_ctrl.sv")
    copyfile(rtl_path + "/rstmgr_por.sv", "rstmgr_por.sv")
    copyfile(rtl_path + "/rstmgr_info.sv", "rstmgr_info.sv")

    # list of core files to be generated
    cores = []

    # rstmgr register core
    core = OrderedDict()
    core["path"] = os.path.abspath("rstmgr_reg.core")
    core["text"] = {
        'name': "lowrisc:ip_gen:rstmgr_reg:0.1",
        'filesets': {
            'files_rtl': {
                'depend': [
                    "lowrisc:tlul:headers",
                ],
                'files': [
                    "rstmgr_reg_pkg.sv",
                    "rstmgr_reg_top.sv",
                ],
                'file_type': 'systemVerilogSource'
            },
        },
        'targets': {
            'default': {
                'filesets': [
                    'files_rtl',
                ],
            },
        },
    }
    cores.append(core)

    # rstmgr package core
    core = OrderedDict()
    core["path"] = os.path.abspath("rstmgr_pkg.core")
    core["text"] = {
        'name': "lowrisc:ip_gen:rstmgr_pkg:0.1",
        'filesets': {
            'files_rtl': {
                'depend': [
                    "lowrisc:constants:top_pkg",
                    "lowrisc:ip_gen:rstmgr_reg",
                    "lowrisc:ip:pwrmgr_pkg",
                ],
                'files': [
                    "rstmgr_pkg.sv",
                ],
                'file_type': 'systemVerilogSource'
            },
        },
        'targets': {
            'default': {
                'filesets': [
                    'files_rtl',
                ],
            },
        },
    }
    cores.append(core)

    # rstmgr package core
    core = OrderedDict()
    core["path"] = os.path.abspath("rstmgr_component.core")
    core["text"] = {
        'name': "lowrisc:ip_gen:rstmgr_component:0.1",
        'filesets': {
            'files_rtl': {
                'depend': [
                    "lowrisc:ip:tlul",
                    "lowrisc:ip_gen:rstmgr_reg",
                    "lowrisc:ip_gen:rstmgr_pkg",
                ],
                'files': [
                    "rstmgr_ctrl.sv",
                    "rstmgr_por.sv",
                    "rstmgr_info.sv",
                ],
                'file_type': 'systemVerilogSource'
            },
        },
        'targets': {
            'default': {
                'filesets': [
                    'files_rtl',
                ],
            },
        },
    }
    cores.append(core)


    print("cores {}".format(cores))

    for core in cores:
        with open(core['path'], 'w') as f:
            f.write("CAPI=2:\n")
            yaml.dump(core['text'],
                      f,
                      encoding="utf-8")
            print("core file written to {}".format(core['path']))


if __name__ == '__main__':
    main()
