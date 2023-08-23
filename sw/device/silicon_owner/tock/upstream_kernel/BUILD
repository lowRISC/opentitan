# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_binary")
load("//rules:linker.bzl", "ld_library")
load("//rules:opentitan.bzl", "elf_to_disassembly", "obj_transform")

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
        "@tock//boards/opentitan/earlgrey-cw310:kernel_srcs",
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
    # We don't want to build the kernel automatically if matched
    # by a bazel wildcard because the kernel will not fit in the allocated
    # space if built in `fastbuild` or `dbg` modes.
    tags = ["manual"],
    deps = [
        ":layout",
        ":nostartfiles",
        "@tock//arch/rv32i",
        "@tock//boards/components",
        "@tock//capsules/aes_gcm:capsules-aes-gcm",
        "@tock//capsules/core:capsules-core",
        "@tock//capsules/extra:capsules-extra",
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
