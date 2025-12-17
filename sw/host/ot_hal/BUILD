# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_doc", "rust_library", "rust_test")
load("//hw/top:defs.bzl", "opentitan_select_top")

package(default_visibility = ["//visibility:public"])

rust_library(
    name = "ot_hal",
    srcs = [
        "src/dif/aon_timer.rs",
        "src/dif/lc_ctrl.rs",
        "src/dif/mod.rs",
        "src/dif/otp_ctrl.rs",
        "src/dif/rstmgr.rs",
        "src/dif/uart.rs",
        "src/lib.rs",
        "src/top/autogen/mod.rs",
        "src/top/mod.rs",
        "src/util/alert.rs",
        "src/util/bitfield.rs",
        "src/util/mod.rs",
        "src/util/multibits.rs",
        "src/util/unknown.rs",
    ] + opentitan_select_top(
        {
            "englishbreakfast": [],
        },
        [
            "src/dif/clkmgr.rs",
            "src/dif/pinmux.rs",
            "src/top/autogen/earlgrey.rs",
        ],
    ),
    crate_features = opentitan_select_top(
        {
            "englishbreakfast": ["english_breakfast"],
        },
        [],
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen/chip:top_earlgrey",
        "//sw/host/ot_hal/bindgen",
        "@crate_index//:anyhow",
        "@crate_index//:bitflags",
        "@crate_index//:clap",
        "@crate_index//:serde",
        "@crate_index//:serde_json",
        "@crate_index//:strum",
        "@crate_index//:thiserror",
    ],
)

rust_test(
    name = "ot_hal_test",
    crate = ":ot_hal",
)

rust_doc(
    name = "ot_hal_doc",
    crate = ":ot_hal",
)
