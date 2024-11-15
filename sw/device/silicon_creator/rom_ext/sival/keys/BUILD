# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:signing.bzl", "keyset")

package(default_visibility = ["//visibility:public"])

# TODO(#22155, #18313): Decide on keyset vs. keyinfo for supplying signing info to the
# offline/token signing flows.  Currently, only keyset supports tokens.

keyset(
    name = "keyset",
    build_setting_default = "",
    keys = {
        "sv00-app-key-prod-0.pub.der": "sv00-app-key-prod-0",
        "sv00-app-key-dev-0.pub.der": "sv00-app-key-dev-0",
        "sv00-app-key-test-0.pub.der": "sv00-app-key-test-0",
    },
    profile = "earlgrey_a1_sival_owner",
    tool = "//signing:token",
)
