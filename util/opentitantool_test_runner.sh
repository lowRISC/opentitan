#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# A shell script for executing opentitantool as the test harness for
# functional tests.

set -e

readonly OPENTITANTOOL="sw/host/opentitantool/opentitantool"
RUST_BACKTRACE=1 ${OPENTITANTOOL} "$@"
