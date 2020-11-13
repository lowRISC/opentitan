#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# The purpose of this simple script is to remove all auto-generated files for
# the current top-level design. Except for top_earlgrey, we anyway don't check
# these files into the repo. This is also useful for debugging topgen by
# letting it run on a clean directory.

# Get the path to the top-specific directory.
top_path=$(dirname $(realpath $0))/../

# Find and delete autogen directories.
find ${top_path} -depth -type d -name "autogen" -exec rm -rf {} \;

# Some autogen files are not in autogen folders.
rm -rf ${top_path}/ip/alert_handler/dv/alert_handler_env_pkg__params.sv
rm -rf ${top_path}/ip/sensor_ctrl/rtl/*
rm -rf ${top_path}/ip/xbar_main/xbar_main.core
rm -rf ${top_path}/ip/xbar_peri/xbar_peri.core
