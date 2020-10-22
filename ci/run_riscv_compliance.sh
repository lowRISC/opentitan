#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
set -e

. util/build_consts.sh

export TARGET_SIM="$BIN_DIR/hw/top_earlgrey/Vtop_earlgrey_verilator"
export RISCV_DEVICE=rv32imc
export RISCV_TARGET=opentitan
export OT_BIN="$BIN_DIR"
export OT_TARGET=sim_verilator
export OT_TOOLS="${TOOLCHAIN_PATH:-/tools/riscv}/bin"

make -C "$REPO_TOP/sw/vendor/riscv_compliance" RISCV_ISA="$1" VERBOSE=1

