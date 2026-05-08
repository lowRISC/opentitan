# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Version requirements for various tools. Checked by tooling (e.g. fusesoc),
# and inserted into the Sphinx-generated documentation.
__TOOL_REQUIREMENTS__ = {
    'verilator': '4.210',
    'edalize':   '0.2.0',
    'vcs': {
        'min_version': '2020.03-SP2',
        'as_needed': True
    },
    'vivado': {
        'min_version': '2020.2',
        'as_needed': True
    },
}
