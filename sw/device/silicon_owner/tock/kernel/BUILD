# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")
load("//rules:linker.bzl", "ld_library")
load("//rules:opentitan.bzl", "OPENTITAN_CPU", "elf_to_disassembly", "obj_transform")

package(default_visibility = ["//visibility:public"])

ld_library(
    name = "kernel_layout",
    includes = [
        "@tock//boards:kernel_layout",
    ],
)

ld_library(
    name = "layout",
    script = "layout.ld",
    deps = [
        ":kernel_layout",
    ],
)

cc_library(
    name = "nostartfiles",
    linkopts = [
        "-nostartfiles",
    ],
)

rust_binary(
    name = "kernel",
    srcs = [
        "src/io.rs",
        "src/main.rs",
        "src/otbn.rs",
        "src/pinmux_layout.rs",
    ],
    rustc_flags = [
        "-g",
        # TODO(opentitan#19491): determine the appropriate set of linker flags.
        #"-Clinker=rust-lld",
        #"-Clinker-flavor=ld.lld",
        #"-Crelocation-model=static",
        #"-Clink-arg=-nmagic",
        #"-Clink-arg=-icf=all",
        #"-Cforce-frame-pointers=no",
    ],
    # We specifically restrict our build target to the OpenTitan
    # CPU because tock does not support an x86_64 target.
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":layout",
        ":nostartfiles",
        "@tock//arch/rv32i",
        "@tock//boards/components",
        "@tock//capsules/aes_gcm:capsules-aes-gcm",
        "@tock//capsules/core:capsules-core",
        "@tock//capsules/extra:capsules-extra",
        "@tock//capsules/system:capsules-system",
        "@tock//chips/earlgrey",
        "@tock//chips/lowrisc",
        "@tock//kernel",
        "@tock//libraries/tock-tbf",
    ],
)

obj_transform(
    name = "raw_kernel",
    srcs = [":kernel"],
    tags = ["manual"],
)
