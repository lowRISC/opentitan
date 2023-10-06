# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:const.bzl", "CONST", "hex")
load("//rules:manifest.bzl", "manifest")

package(default_visibility = ["//visibility:public"])

manifest({
    "name": "manifest_standard",
    "address_translation": hex(CONST.HARDENED_FALSE),
    "identifier": hex(CONST.OWNER),
    "visibility": ["//visibility:public"],
})
