#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

#  1. Changes 'chip_earlgrey_asic' interface port lines:
#     inout CC1, // Manual Pad
#     inout CC2, // Manual Pad
#  ...
#     inout IOA2, // MIO Pad 2
#     inout IOA3, // MIO Pad 3
#
#  To:
#     `INOUT_AI CC1, // Manual Pad
#     `INOUT_AI CC2, // Manual Pad
#  ...
#     `INOUT_AO IOA2, // MIO Pad 2
#     `INOUT_AO IOA3, // MIO Pad 3
#
#  2. Changes 'u_padring' instance ports lines:
#        CC2,
#        CC1,
#  ...
#        IOA3,
#        IOA2,
#
#  To:
#        `CC2_A,
#        `CC1_A,
#  ...
#        `IOA3_A,
#        `IOA2_A,

import re
import shutil

input_file = "top_earlgrey/rtl/autogen/chip_earlgrey_asic.sv"
# Keep the original file for reference
shutil.copy(input_file, "".join([input_file, ".orig"]))

with open(input_file, "r") as rfile:
    s = rfile.read()

s = re.sub(r'(^\s+)inout CC1,', r'\1`INOUT_AI CC1,', s, flags=re.M)
s = re.sub(r'(^\s+)inout CC2,', r'\1`INOUT_AI CC2,', s, flags=re.M)
s = re.sub(r'(^\s+)inout IOA2,', r'\1`INOUT_AO IOA2,', s, flags=re.M)
s = re.sub(r'(^\s+)inout IOA3,', r'\1`INOUT_AO IOA3,', s, flags=re.M)
s = re.sub(r'(^\s+)CC2,', r'\1`CC2_A,', s, flags=re.M)
s = re.sub(r'(^\s+)CC1,', r'\1`CC1_A,', s, flags=re.M)
s = re.sub(r'(^\s+)IOA3,', r'\1`IOA3_A,', s, flags=re.M)
s = re.sub(r'(^\s+)IOA2,', r'\1`IOA2_A,', s, flags=re.M)

with open(input_file, "w") as wfile:
    wfile.write(s)
