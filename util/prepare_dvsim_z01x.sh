#!/bin/bash

# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This script copies proprietary Synopsys Z01X scripts that are located
# in the private https://github.com/lowRISC/opentitan_fi_z01x repository
# into the public OpenTitan repostitory.
# Before starting any Z01X simulations with DVSIM, run this script.
#
# Please refer to hw/dv/tools/z01x/README.md for further information.
#
# Usage:
#   git clone git@github.com:lowRISC/opentitan_fi_z01x.git
#   git clone git@github.com:lowRISC/opentitan.git
#   export Z01X_DIR=<path to the opentitan_fi_z01x directory>
#   export OT_DIR=<path to the opentitan directory>
#   cd opentitan/
#   ./util/prepare_dvsim_z01x.sh

if [[ -z "${Z01X_DIR}" ]]; then
  echo "Z01X_DIR environment variable not set." >&2
  exit 1
else
  SRC_DIR="${Z01X_DIR}"
fi

if [[ -z "${OT_DIR}" ]]; then
  echo "OT_DIR environment variable not set." >&2
  exit 1
else
  DST_DIR="${OT_DIR}"
fi

echo "Copying ${SRC_DIR} into ${DST_DIR}"
cp -R $SRC_DIR/hw $DST_DIR/
