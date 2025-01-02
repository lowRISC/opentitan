# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")

package(default_visibility = ["//visibility:public"])

rust_binary(
    name = "csr_rw",
    srcs = [
        "src/csr_rw.rs",
    ],
    deps = [
        "//hw/top_earlgrey/sw/autogen/chip:top_earlgrey",
        "//sw/host/opentitanlib",
        "//sw/host/opentitanlib/bindgen",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:rand",
        "@crate_index//:rand_chacha",
    ],
)

rust_binary(
    name = "mem_access",
    srcs = [
        "src/mem_access.rs",
    ],
    deps = [
        "//hw/top_earlgrey/sw/autogen/chip:top_earlgrey",
        "//sw/host/opentitanlib",
        "//sw/host/opentitanlib/bindgen",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:rand",
        "@crate_index//:rand_chacha",
    ],
)

rust_binary(
    name = "jtag",
    srcs = [
        "src/jtag.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:log",
    ],
)

rust_binary(
    name = "jtag_tap_sel",
    srcs = [
        "src/jtag_tap_sel.rs",
    ],
    deps = [
        "//hw/top_earlgrey/sw/autogen/chip:top_earlgrey",
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:log",
        "@crate_index//:once_cell",
        "@crate_index//:regex",
    ],
)

rust_binary(
    name = "lc_disabled",
    srcs = [
        "src/lc_disabled.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:log",
        "@crate_index//:rand",
    ],
)

rust_binary(
    name = "ndm_reset_req",
    srcs = [
        "src/ndm_reset_req.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
    ],
)

rust_binary(
    name = "ndm_reset_req_when_cpu_halted",
    srcs = [
        "src/ndm_reset_req_when_cpu_halted.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
    ],
)

rust_binary(
    name = "dtm",
    srcs = [
        "src/dtm.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:rand",
    ],
)

rust_binary(
    name = "control_status",
    srcs = [
        "src/control_status.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
    ],
)

rust_binary(
    name = "access_after_wakeup",
    srcs = [
        "src/access_after_wakeup.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:object",
        "@crate_index//:rand",
    ],
)

rust_binary(
    name = "access_after_hw_reset",
    srcs = [
        "src/access_after_hw_reset.rs",
    ],
    deps = [
        "//sw/host/opentitanlib",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:object",
    ],
)
