#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Converts mubi mako templates
"""
from mubi import prim_mubi
from secded_gen import format_c_files

def main():
    prim_mubi.gen()
    c_path = prim_mubi.get_c_path()

    format_c_files(c_path, c_path)

if __name__ == "__main__":
    main()
