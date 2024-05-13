#!/bin/bash

# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

./ci/scripts/check_dv_sw_images.py \
    hw/top_earlgrey/dv/chip_sim_cfg.hjson \
    hw/top_earlgrey/dv/chip_rom_tests.hjson \
    hw/top_earlgrey/dv/chip_smoketests.hjson
