#!/usr/bin/python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from distutils.version import StrictVersion
import logging as log
import os
import re
import subprocess
import sys

# Display INFO log messages and up.
log.basicConfig(level=log.INFO, format="%(levelname)s: %(message)s")


def get_tool_requirements_path():
    '''Return the path to tool_requirements.py, at the top of the repo'''
    # top_src_dir is the top of the repository
    top_src_dir = os.path.normpath(os.path.join(os.path.dirname(__file__),
                                                '..'))

    return os.path.join(top_src_dir, 'tool_requirements.py')


def read_tool_requirements(path=None):
    '''Read tool requirements from a Python file'''
    if path is None:
        path = get_tool_requirements_path()

    with open(path, 'r') as pyfile:
        globs = {}
        exec(pyfile.read(), globs)

        # We expect the exec call to have populated globs with a
        # __TOOL_REQUIREMENTS__ dictionary.
        reqs = globs.get('__TOOL_REQUIREMENTS__')
        if reqs is None:
            log.error('The Python file at {} did not define '
                      '__TOOL_REQUIREMENTS__.'
                      .format(path))
            return None

        # reqs should be a dictionary (mapping tool name to minimum version)
        if not isinstance(reqs, dict):
            log.error('The Python file at {} defined '
                      '__TOOL_REQUIREMENTS__, but it is not a dict.'
                      .format(path))
            return None

        return reqs


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


def pip3_get_version(tool):
    '''Run pip3 to find the version of an installed module'''
    cmd = ['pip3', 'show', tool]
    try:
        proc = subprocess.run(cmd,
                              check=True,
                              stderr=subprocess.STDOUT,
                              stdout=subprocess.PIPE,
                              universal_newlines=True)
    except subprocess.CalledProcessError as err:
        log.error('pip3 command failed: {}'.format(err))
        log.error("Failed to get version of {} with pip3: is it installed?"
                  .format(tool))
        log.error(err.stdout)
        return None

    version_re = 'Version: (.*)'
    for line in proc.stdout.splitlines():
        match = re.match(version_re, line)
        if match:
            return match.group(1)

    # If we get here, we never saw a version line.
    log.error('No output line from running {} started with "Version: ".'
              .format(cmd))
    return None


def check_version(requirements, tool_name, getter):
    required_version = requirements.get(tool_name)
    if required_version is None:
        log.error('Requirements file does not specify version for {}.'
                  .format(tool_name))
        return False

    actual_version = getter()
    if actual_version is None:
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
    # Get tool requirements
    tool_requirements = read_tool_requirements()
    if tool_requirements is None:
        return 1

    all_good = True
    all_good &= check_version(tool_requirements,
                              'verilator',
                              get_verilator_version)
    all_good &= check_version(tool_requirements,
                              'edalize',
                              lambda: pip3_get_version('edalize'))

    if not all_good:
        log.error("Tool requirements not fulfilled. "
                  "Please update the tools and retry.")
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main())
