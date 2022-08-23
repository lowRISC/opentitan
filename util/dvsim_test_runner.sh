#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# A shell script for executing dvsim.py as the test harness for functional
# tests.

set -e

readonly DVSIM="util/dvsim/dvsim.py"

echo "At this time, dvsim.py must be run manually (after building SW) via:
${DVSIM} $* ${TEST_CMDS} "
