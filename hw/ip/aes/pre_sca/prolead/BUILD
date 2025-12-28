# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

exports_files(["library.lib"])

filegroup(
    name = "config_file",
    srcs = ["aes_cipher_core_config.set"],
)

# The Bazel run rule to build the aes_cipher_core netlist and run prolead
# for 6M traces.
sh_binary(
    name = "full_evaluate_aes_cipher_core",
    srcs = ["evaluate.sh"],
    data = [
        "library.lib",
        ":config_file",
        "//hw/ip/aes/pre_syn:aes_cipher_core_netlist.v",
        "@prolead//:prolead_binary",
    ],
    env = {
        "PROLEAD_BIN": "$(location @prolead//:prolead_binary)",
        "NETLIST_FILE": "$(location //hw/ip/aes/pre_syn:aes_cipher_core_netlist.v)",
        "LIBRARY_FILE": "$(location library.lib)",
        "CONFIG_FILE": "$(location :config_file)",
    },
    deps = ["@bazel_tools//tools/bash/runfiles"],
)
