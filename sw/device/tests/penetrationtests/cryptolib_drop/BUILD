# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This folder serves as a skeleton directory to place a cryptolib drop (binary and header files) for a pentest with a prebuild library.
# To use, simply move the crypto folder in this directory.

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "cryptolib_imported",
    # Empty list if there is no drop present to stop Bazel from crashing.
    srcs = glob(
        ["crypto/libotcrypto.a"],
        allow_empty = True,
    ),
    hdrs = glob(
        [
            "crypto/include/*.h",
            "crypto/include/freestanding/*.h",
        ],
        allow_empty = True,
    ),
    include_prefix = "sw/device/lib/crypto/include",
    strip_include_prefix = "crypto/include",
)

# This is the flag for either using the internal cryptolib or a prebuilt cryptolib.
config_setting(
    name = "use_prebuilt_cryptolib",
    define_values = {
        "cryptolib": "prebuilt",
    },
)
