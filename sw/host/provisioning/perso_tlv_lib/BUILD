# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//bindgen:bindgen.bzl", "rust_bindgen_library")
load("@rules_rust//rust:defs.bzl", "rust_library")

package(default_visibility = ["//visibility:public"])

rust_bindgen_library(
    name = "perso_tlv_objects",
    bindgen_flags = [
        "--allowlist-type=perso_tlv_object_type_t",
        "--allowlist-type=perso_tlv_object_header_t",
        "--allowlist-type=perso_tlv_cert_header_t",
        "--allowlist-type=perso_tlv_dev_seed_header_t",
        "--allowlist-type=perso_tlv_obj_header_fields_t",
        "--allowlist-type=perso_tlv_cert_header_fields_t",
    ],
    cc_lib = "//sw/device/silicon_creator/manuf/base:perso_tlv_headers",
    header = "//sw/device/silicon_creator/manuf/base:perso_tlv_data.h",
    rustc_flags = [
        "--allow=non_snake_case",
        "--allow=non_upper_case_globals",
        "--allow=non_camel_case_types",
    ],
)

rust_library(
    name = "perso_tlv_lib",
    srcs = ["src/lib.rs"],
    deps = [
        "//sw/host/provisioning/perso_tlv_lib:perso_tlv_objects",
        "@crate_index//:anyhow",
    ],
)
