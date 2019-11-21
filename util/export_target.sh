#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

# export_target.sh is intended to be invoked by Meson, to work around Meson's
# limitations for custom_target() (it is not possible to specify more than one
# command) and limitations on string handling (Meson does not provide
# standard string manipulation functions like trim_prefix()).
#
# This script does not use build_consts.sh, but relies on Meson to supply that
# information.

platform_bin_dir="$1"; shift
meson_src_dir_prefix="$1"; shift
meson_src_dir="$1"; shift

target_bin_dir="$platform_bin_dir/${meson_src_dir#"$meson_src_dir_prefix"}"

mkdir -p "$target_bin_dir"
cp $@ "$target_bin_dir"
