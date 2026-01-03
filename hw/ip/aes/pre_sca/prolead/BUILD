# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

exports_files(["library.lib"])

filegroup(
    name = "aes_cipher_core_config_file",
    srcs = ["aes_cipher_core_config.set"],
)

filegroup(
    name = "aes_cipher_core_config_ci_file",
    srcs = ["aes_cipher_core_config_ci.set"],
)

# The Bazel run rule to build the aes_cipher_core netlist and run prolead
# for 6M traces.
sh_binary(
    name = "full_evaluate_aes_cipher_core",
    srcs = ["evaluate.sh"],
    data = [
        "library.lib",
        ":aes_cipher_core_config_file",
        "//hw/ip/aes/pre_syn:aes_cipher_core_netlist.v",
        "@prolead//:prolead_binary",
    ],
    env = {
        "PROLEAD_BIN": "$(location @prolead//:prolead_binary)",
        "NETLIST_FILE": "$(location //hw/ip/aes/pre_syn:aes_cipher_core_netlist.v)",
        "LIBRARY_FILE": "$(location library.lib)",
        "CONFIG_FILE": "$(location :aes_cipher_core_config_file)",
    },
    tags = ["manual"],
    deps = ["@bazel_tools//tools/bash/runfiles"],
)

# The Bazel run rule for the CI evaluation of the aes_cipher_core for side-channel analysis.
sh_test(
    name = "ci_evaluate_aes_cipher_core",
    srcs = ["evaluate.sh"],
    data = [
        "library.lib",
        ":aes_cipher_core_config_ci_file",
        "//hw/ip/aes/pre_syn:aes_cipher_core_netlist.v",
        "@prolead//:prolead_binary",
    ],
    env = {
        "PROLEAD_BIN": "$(location @prolead//:prolead_binary)",
        "NETLIST_FILE": "$(location //hw/ip/aes/pre_syn:aes_cipher_core_netlist.v)",
        "LIBRARY_FILE": "$(location library.lib)",
        "CONFIG_FILE": "$(location :aes_cipher_core_config_ci_file)",
        # We put a high threshold to have an extremely low probability for a false positive.
        "MAX_LEAKAGE_THRESHOLD": "8.0",
    },
    tags = [
        "nightly",
    ],
    deps = ["@bazel_tools//tools/bash/runfiles"],
)
