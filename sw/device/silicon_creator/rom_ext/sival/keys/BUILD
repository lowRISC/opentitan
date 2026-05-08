# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:signing.bzl", "keyset")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "includes",
    hdrs = [
        "appkey_dev_0.h",
        "appkey_prod_0.h",
        "appkey_test_0.h",
        "earlgrey_z0_sival_1.h",
        "ownership_activate_key.h",
        "ownership_owner_key.h",
        "ownership_unlock_key.h",
    ],
)

keyset(
    name = "keyset",
    build_setting_default = "",
    keys = {
        "earlgrey_z0_sival_1.der": "earlgrey_z0_sival_1",
        "appkey_dev_0.der": "appkey_dev_0",
        "appkey_prod_0.der": "appkey_prod_0",
        "appkey_test_0.der": "appkey_test_0",
    },
    profile = "earlgrey_z0_sival",
    tool = "//signing:token",
)
