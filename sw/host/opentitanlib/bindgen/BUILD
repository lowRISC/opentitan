# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")
load("@rules_rust//bindgen:bindgen.bzl", "rust_bindgen_library")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "difs",
    hdrs = ["difs.h"],
    deps = [
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:rstmgr",
    ],
)

rust_bindgen_library(
    name = "alert",
    bindgen_flags = [
        "--allowlist-type=AlertClass",
        "--allowlist-type=AlertEnable",
        "--allowlist-type=AlertEscalate",
    ],
    cc_lib = "//sw/device/silicon_creator/lib/drivers:alert",
    header = "//sw/device/silicon_creator/lib/drivers:alert.h",
    rustc_flags = [
        "--allow=non_snake_case",
        "--allow=non_upper_case_globals",
    ],
)

rust_bindgen_library(
    name = "dif",
    bindgen_flags = [
        "--allowlist-var=CLKMGR_.*_BIT",
        "--allowlist-var=CLKMGR_.*_REG_OFFSET",
        "--allowlist-var=CLKMGR_.*_MASK",
        "--allowlist-var=CLKMGR_.*_OFFSET",
        "--allowlist-type=dif_lc_ctrl_state",
        "--allowlist-type=dif_lc_ctrl_token",
        "--allowlist-var=LC_CTRL_.*_BIT",
        "--allowlist-var=LC_CTRL_.*_REG_OFFSET",
        "--allowlist-type=dif_rstmgr_reset_info",
    ],
    cc_lib = ":difs",
    header = "difs.h",
    rustc_flags = [
        "--allow=non_snake_case",
        "--allow=non_upper_case_globals",
        "--allow=non_camel_case_types",
    ],
)

rust_bindgen_library(
    name = "earlgrey",
    bindgen_flags = [
        "--allowlist-type=top_earlgrey_alert_peripheral",
        "--allowlist-type=top_earlgrey_alert_id",
        "--allowlist-type=top_earlgrey_pinmux_peripheral_in",
        "--allowlist-type=top_earlgrey_pinmux_insel",
        "--allowlist-type=top_earlgrey_pinmux_mio_out",
        "--allowlist-type=top_earlgrey_pinmux_outsel",
        "--allowlist-type=top_earlgrey_direct_pads",
        "--allowlist-type=top_earlgrey_muxed_pads",
        "--allowlist-type=top_earlgrey_power_manager_wake_ups",
        "--allowlist-type=top_earlgrey_reset_manager_sw_resets",
        "--allowlist-type=top_earlgrey_power_manager_reset_requests",
        "--allowlist-type=top_earlgrey_gateable_clocks",
        "--allowlist-type=top_earlgrey_hintable_clocks",
    ],
    cc_lib = "//hw/top_earlgrey/sw/autogen:top_earlgrey",
    header = "//hw/top_earlgrey/sw/autogen:top_earlgrey.h",
    rustc_flags = [
        "--allow=non_snake_case",
        "--allow=non_upper_case_globals",
        "--allow=non_camel_case_types",
    ],
)

rust_bindgen_library(
    name = "hardened",
    bindgen_flags = [
        "--allowlist-type=hardened_bool",
        "--allowlist-type=hardened_byte_bool",
    ],
    cc_lib = "//sw/device/lib/base:hardened",
    header = "//sw/device/lib/base:hardened.h",
    rustc_flags = [
        "--allow=non_snake_case",
        "--allow=non_upper_case_globals",
        "--allow=non_camel_case_types",
    ],
)

rust_bindgen_library(
    name = "multibits",
    bindgen_flags = [
        "--allowlist-type=multi_bit_bool",
    ],
    cc_lib = "//sw/device/lib/base:multibits",
    header = "//sw/device/lib/base:multibits.h",
    rustc_flags = [
        "--allow=non_snake_case",
        "--allow=non_upper_case_globals",
        "--allow=non_camel_case_types",
    ],
)

rust_library(
    name = "bindgen",
    srcs = ["lib.rs"],
    deps = [
        ":alert",
        ":dif",
        ":earlgrey",
        ":hardened",
        ":multibits",
    ],
)
