# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

exports_files(glob(["veri-titan/gen/*.s"]))

cc_library(
    name = "cryptoc_sha256",
    srcs = ["cryptoc/sha256.c"],
    hdrs = [
        "cryptoc/include/cryptoc/hash-internal.h",
        "cryptoc/include/cryptoc/sha256.h",
    ],
    strip_include_prefix = "cryptoc/include",
)

filegroup(
  name = "llvm_clang_rt_profile",
  srcs = glob(
      ["llvm_clang_rt_profile/compiler-rt/**/*"],
      exclude = [
          "llvm_clang_rt_profile/compiler-rt/*.TXT",
          "llvm_clang_rt_profile/compiler-rt/.gitignore",
      ]
  ),
)
