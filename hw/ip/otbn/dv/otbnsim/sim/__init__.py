# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import os
import sys


# Ensure that the OTBN util directory is on sys.path. This allows us to import
# modules "shared.foo" to get the OTBN shared code.
sys.path.append(os.path.normpath(os.path.join(os.path.dirname(__file__),
                                              '../../../util')))
