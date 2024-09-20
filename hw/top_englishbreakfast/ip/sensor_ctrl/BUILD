# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "all_files",
    srcs = glob(["**"]) + [
        "//hw/top_englishbreakfast/ip/sensor_ctrl/data:all_files",
        # We simply alias everything to earlgrey.
        "//hw/top_earlgrey/ip/sensor_ctrl:all_files",
    ],
)
