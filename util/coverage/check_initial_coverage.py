#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import sys

with open(sys.argv[1], 'rb') as f:
    data = f.read()

# Remove gap fill
data = data.rstrip(b'\xa5')

# Asserts the section are all 0xff (uncovered).
assert data.strip(b'\xff') == b'', data

# Bazel's action requires an output.
with open(sys.argv[2], 'w') as f:
    f.write('ok')
