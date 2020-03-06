#!/usr/bin/python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from distutils.version import StrictVersion
import logging as log
import os
import subprocess
import sys

# Display INFO log messages and up.
log.basicConfig(level=log.INFO, format="%(levelname)s: %(message)s")

# Populate __TOOL_REQUIREMENTS__
topsrcdir = os.path.join(os.path.dirname(__file__), '..')
exec(open(os.path.join(topsrcdir, 'tool_requirements.py')).read())

def get_verilator_version():
    try:
        # Note: "verilator" needs to be called through a shell and with all
        # arguments in a string, as it doesn't have a shebang, but instead
        # relies on perl magic to parse command line arguments.
        version_str = subprocess.run('verilator --version', shell=True,
                                     check=True, stdout=subprocess.PIPE,
                                     stderr=subprocess.STDOUT,
                                     universal_newlines=True)
        return version_str.stdout.split(' ')[1].strip()

    except subprocess.CalledProcessError as e:
        log.error("Unable to call Verilator to check version: " + str(e))
        log.error(e.stdout)
        return None

def check_version(tool_name, required_version, actual_version):
    if required_version is None or actual_version is None:
        return False

    if StrictVersion(actual_version) < StrictVersion(required_version):
        log.error("%s is too old: found version %s, need at least %s",
                  tool_name, actual_version, required_version)
        return False
    else:
        log.info("Found sufficiently recent version of %s (found %s, need %s)",
                 tool_name, actual_version, required_version)
        return True


def main():
    any_failed = False

    if not check_version('verilator', __TOOL_REQUIREMENTS__['verilator'],
                         get_verilator_version()):
        any_failed = True

    if any_failed:
        log.error("Tool requirements not fulfilled. "
                  "Please update the tools and retry.")
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
