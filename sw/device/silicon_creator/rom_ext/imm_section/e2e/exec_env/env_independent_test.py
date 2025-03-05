#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from pathlib import Path

binaries = list(Path('.').glob('**/*.bin'))
assert len(binaries) > 2

contents = [path.read_bytes() for path in binaries]
assert len(set(contents)) == 1, "Immutable ROM_EXT is not exec env independent"
