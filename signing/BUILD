# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

label_flag(
    name = "token",
    build_setting_default = "//signing/tokens:local",
)

config_setting(
    name = "test_keys",
    flag_values = {
        ":token": "//signing/tokens:local",
    },
)

filegroup(
    name = "none_key",
    srcs = ["skip.bit"],
)
