# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Targets for a lowRISC toolchain release."""

load("@bazel_skylib//rules/directory:directory.bzl", "directory")
load("@bazel_skylib//rules/directory:subdirectory.bzl", "subdirectory")
load("@rules_cc//cc/toolchains:tool.bzl", "cc_tool")

def lowrisc_toolchain_targets(clang_version, llvm_tools = []):
    """Declares the targets of a lowRISC toolchain release.

    Args:
      clang_version: Major version of the bundled clang, which names its
        resource directory.
      llvm_tools: `llvm-` prefixed tools to expose in addition to the
        `riscv32-unknown-elf-` ones.
    """

    native.exports_files(native.glob(["**"]))

    # Define certain binaries as `cc_tool`s so they can be used in a toolchain.
    # Each tool has access to all the other libraries and binaries in this
    # repository because some tools execute one another and access various
    # libraries.
    for tool in [
        "clang",
        "clang++",
        "ar",
        "nm",
        "objcopy",
        "objdump",
        "strip",
    ]:
        cc_tool(
            name = tool,
            src = ":bin/riscv32-unknown-elf-{}".format(tool),
            data = [":root"],
        )

    for tool in ["profdata", "cov"] + llvm_tools:
        cc_tool(
            name = "llvm_{}".format(tool),
            src = ":bin/llvm-{}".format(tool),
            data = [":root"],
        )

    directory(
        name = "root",
        srcs = native.glob(["**/*"]),
    )

    # System library include directories (for `-isystem`):
    subdirectory(
        name = "lib-clang-include",
        parent = ":root",
        path = "lib/clang/{}/include".format(clang_version),
    )
