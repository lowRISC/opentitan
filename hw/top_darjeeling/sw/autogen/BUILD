# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:linker.bzl", "ld_library")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "top_darjeeling",
    srcs = [
        "top_darjeeling.c",
    ],
    hdrs = [
        "top_darjeeling.h",
        "top_darjeeling_memory.h",
        # TODO(opentitan-integrated/issues/332): dummy definitions added as
        # a workaround so that the flash_ctrl can be removed without having to
        # refactor all dependent tests and the ROM at once. This needs to be
        # cleaned up and removed. Note that the SW depending on flash_ctrl
        # is currently not functional.
        "top_darjeeling_flash_ctrl_dummy.h",
        # TODO(opentitan-integrated/issues/145): dummy definitions added as
        # a workaround so that the the old keymgr can be removed without having to
        # refactor all dependent tests and the ROM at once. These tests and the DIF
        # need to be refactored so that they work with keymgr_dpe instead.
        #  Note that the SW depending on the old keymgr is currently not functional.
        "top_darjeeling_keymgr_dummy.h",
    ],
)

ld_library(
    name = "top_darjeeling_memory",
    includes = ["top_darjeeling_memory.ld"],
)

filegroup(
    name = "all_files",
    srcs = glob(["**"]),
)
