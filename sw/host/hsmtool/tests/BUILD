# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

sh_test(
    name = "token_exists_test",
    srcs = ["hsmtool_runner.sh"],
    args = [
        "--module=$(rootpath @softhsm2//:gen_dir)/lib/softhsm/libsofthsm2.so",
        "--token=fake_keys",
        "token",
        "list",
    ],
    data = [
        "//signing/softhsm",
        "//signing/softhsm:conf",
        "//sw/host/hsmtool",
        "@softhsm2//:gen_dir",
    ],
    env = {
        "SOFTHSM2_CONF": "$(rootpath //signing/softhsm:conf)",
    },
)
