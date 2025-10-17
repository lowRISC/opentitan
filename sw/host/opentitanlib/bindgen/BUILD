# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_library")
load("@rules_rust_bindgen//:defs.bzl", "rust_bindgen", "rust_bindgen_library")

package(default_visibility = ["//visibility:public"])

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

# We generate the bindgen source for rom_error_t so we can post-process it
# with the :rom_error_enum rule and build a full enum from all known
# rom_error_t values.
rust_bindgen(
    name = "rom_error",
    bindgen_flags = [
        "--allowlist-type=rom_error_t",
    ],
    cc_lib = "//sw/device/silicon_creator/lib:error",
    header = "//sw/device/silicon_creator/lib:error.h",
)

# Generate a rust source file that contains the enum definition.  This
# will get textual-included into opentitanlib's `chip::rom_error` module.
genrule(
    name = "rom_error_enum",
    srcs = [":rom_error"],
    outs = ["rom_error_enum.rs"],
    cmd = """
cat >$@ <<HEADER
with_unknown! {
    pub enum RomError: u32 [default = Self::Unknown] {
HEADER

# The sed expression creates enumerators with idiomatic Rust names that
# refer to the bindgen'ed constants.
cat $(location :rom_error) \\
    | grep const \\
    | sed -E 's/^pub const (rom_error_kError([^:]+)).*$$/        \\2 = bindgen::rom_error::\\1,/g' >>$@

cat >>$@ <<FOOTER
    }
}
FOOTER
    """,
)

rust_bindgen_library(
    name = "sram_program",
    bindgen_flags = [
        "--allowlist-var=SRAM_MAGIC_SP_.*",
    ],
    cc_lib = "//sw/device/silicon_creator/manuf/lib:sram_start_headers",
    header = "//sw/device/silicon_creator/manuf/lib:sram_start.h",
    rustc_flags = [
        "--allow=non_snake_case",
        "--allow=non_upper_case_globals",
        "--allow=non_camel_case_types",
    ],
)

rust_bindgen_library(
    name = "status",
    bindgen_flags = [
        "--allowlist-type=ot_status_create_record_t",
        "--allowlist-type=ot_status_create_record_magic",
        "--allowlist-type=status",
        "--allowlist-type=status_t",
        "--allowlist-type=absl_status_t",
        "--allowlist-function=status_create",
        "--allowlist-function=status_extract",
        # status_err and status_ok are marked as always inline but are also
        # declared as extern in status.c which means that will actually end up
        # in the object file.
        "--allowlist-function=status_err",
        "--allowlist-function=status_ok",
        "--generate-inline-functions",
        "--with-derive-custom=ot_status_create_record=zerocopy::FromBytes",
    ],
    cc_lib = "//sw/device/lib/base:status",
    header = "//sw/device/lib/base:status.h",
    rustc_flags = [
        "--allow=non_snake_case",
        "--allow=non_upper_case_globals",
        "--allow=non_camel_case_types",
    ],
    deps = [
        "@crate_index//:zerocopy",
    ],
)

rust_bindgen_library(
    name = "test_status",
    bindgen_flags = [
        "--allowlist-type=test_status_t",
    ],
    cc_lib = "//sw/device/lib/testing/test_framework:status_headers",
    header = "//sw/device/lib/testing/test_framework:status.h",
    rustc_flags = [
        "--allow=non_snake_case",
        "--allow=non_upper_case_globals",
        "--allow=non_camel_case_types",
    ],
)

rust_library(
    name = "bindgen",
    srcs = [
        "lib.rs",
        ":rom_error",
    ],
    deps = [
        ":hardened",
        ":sram_program",
        ":status",
        ":test_status",
    ],
)
