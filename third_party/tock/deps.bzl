# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//third_party/tock/crates:crates.bzl", "raze_fetch_remote_crates")

def tock_deps():
    raze_fetch_remote_crates()
