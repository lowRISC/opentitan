#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import sys
import reggen.gen_selfdoc as reggen_selfdoc
import tlgen
from typing import TextIO


def generate_selfdocs(tool: str, fout: TextIO):
    """Generate documents for the tools in `util/`

    Each tool creates selfdoc differently. Manually invoked.
    """
    if tool == "reggen":
        reggen_selfdoc.document(fout)
    elif tool == "tlgen":
        fout.write(tlgen.selfdoc(heading=3, cmd='tlgen.py --doc'))
    else:
        sys.exit(f"unknown tool \"{tool}\"")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit("usage: selfdoc <tool>")
    # running this file as standalone prints the documentation
    generate_selfdocs(sys.argv[1], sys.stdout)
