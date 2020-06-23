#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

# This script deletes any -I command line arguments that are not
# - Absolute paths.
# - Ephemeral build directories.
#
# This function is necessary because Meson does not give adequate
# control over what directories are passed in as -I search directories
# to the C compiler. While Meson does provide |implicit_include_directories|,
# support for this option is poor: empirically, Meson ignores this option for
# some targerts. Doing it as a post-processing step ensures that Meson does
# not allow improper #includes to compile successfully.
#
# This is run by meson as a postconf script. The following env variables will be
# set:
# - MESON_SOURCE_ROOT
# - MESON_BUILD_ROOT

echo "Purging superfluous -I arguments from $MESON_BUILD_ROOT."
perl -pi -e 's#-I[^/][^@ ]+ # #g' -- "$MESON_BUILD_ROOT/build.ninja"
