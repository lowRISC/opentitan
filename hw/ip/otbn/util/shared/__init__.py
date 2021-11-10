# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import os
import sys

# Ensure that the OpenTitan utils directory is on sys.path. This will allow us
# (and anyone who depends on us) to import serialize.parse_helpers.
#
# This isn't massively clean: in particular, messing around with sys.path like
# this in a library __init__ file can cause havoc with paths. *But* doing it
# properly would either mean installing Python libraries or pasting the lines
# below into every script that wanted to use the utility code.
_OTBN_DIR = os.path.normpath(os.path.join(os.path.dirname(__file__), '../..'))
_OT_DIR = os.path.normpath(os.path.join(_OTBN_DIR, '../../..'))
_OT_UTIL_DIR = os.path.join(_OT_DIR, 'util')
sys.path.append(_OT_UTIL_DIR)
