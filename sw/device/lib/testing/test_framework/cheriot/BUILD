# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//hw/top:defs.bzl", "opentitan_require_top")
load("//rules:linker.bzl", "ld_library")

package(default_visibility = ["//visibility:public"])

ld_library(
    name = "ottf_ld_common",
    includes = ["ottf_common.ld"],
    target_compatible_with = opentitan_require_top("earlgrey"),
    deps = [
        "//sw/device:info_sections",
        "//sw/device/lib/coverage:coverage_sections",
    ],
)

[
    ld_library(
        name = "ottf_ld_{}".format(slot),
        script = "ottf_{}.ld".format(slot),
        target_compatible_with = opentitan_require_top("earlgrey"),
        deps = [
            ":ottf_ld_common",
            "//hw/top:top_ld",
            "//sw/device/lib/testing/test_framework:ottf_ld_top_config",
        ],
    )
    for slot in [
        "silicon_creator_slot_a",
        "silicon_owner_slot_a",
    ]
]
