# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:tock.bzl", "tock_image")

package(default_visibility = ["//visibility:public"])

tock_image(
    name = "image",
    app = "//sw/device/silicon_owner/tock/apps/hello",
    kernel = "//sw/device/silicon_owner/tock/kernel",
)
