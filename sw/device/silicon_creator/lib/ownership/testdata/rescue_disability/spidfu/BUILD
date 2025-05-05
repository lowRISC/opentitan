# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "test_owner",
    srcs = [
        "test_owner.c",
    ],
    textual_hdrs = [":test_owner_h"],
    deps = [
        "//sw/device/silicon_creator/lib:boot_data",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/ownership",
        "//sw/device/silicon_creator/lib/ownership:datatypes",
        "//sw/device/silicon_creator/lib/ownership:owner_block",
    ],
    alwayslink = True,
)

genrule(
    name = "test_owner_h",
    srcs = [
        ":test_owner_bin",
    ],
    outs = ["test_owner.h"],
    cmd = """
        $(execpath //util/sh/scripts:bin2c.sh) \
                --input $(location :test_owner_bin) \
                --output $@ \
                --name test_owner
    """,
    tools = [
        "//util/sh/scripts:bin2c.sh",
        "//util/sh/scripts:c.hexdump",
    ],
)

genrule(
    name = "test_owner_bin",
    srcs = [
        "test_owner.json5",
        "//sw/device/silicon_creator/lib/ownership/keys/fake:all_keys",
    ],
    outs = ["test_owner.bin"],
    cmd = """
        $(execpath //sw/host/opentitantool) --rcfile= \
            ownership config --input $(location :test_owner.json5) $@
    """,
    tools = ["//sw/host/opentitantool"],
)
