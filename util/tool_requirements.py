# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Version requirements for various tools. Checked by tooling (e.g. fusesoc),
# and inserted into the documentation.
#
# Entries are keyed by tool name. The value is either a string giving the
# minimum version number or is a dictionary. If a dictionary, the following
# keys are recognised:
#
#    min_version: Required string. Minimum version number.
#
#    as_needed:   Optional bool. Defaults to False. If set, this tool is not
#                 automatically required. If it is asked for, the rest of the
#                 entry gives the required version.
#
__TOOL_REQUIREMENTS__ = {
    'edalize': '0.2.0',
    'ninja': {
        'min_version': '1.8.2',
        'as_needed': True
    },
    'verilator': {
        'min_version': '4.210',
        'as_needed': True
    },
    'hugo_extended': {
        'min_version': '0.82.0',
        'as_needed': True
    },
    'verible': {
        'min_version': 'v0.0-2135-gb534c1fe',
        'as_needed': True
    },
    'vcs': {
        'min_version': '2022.06-SP2',
        'as_needed': True
    },
    'vivado': {
        'min_version': '2020.2',
        'as_needed': True
    },
}
