# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//rules:common_settings.bzl", "bool_flag", "string_flag")

package(default_visibility = ["//visibility:public"])

exports_files([
    "crypto_fips_all.txt",
    "otcrypto_blob.ld",
    "otcrypto_partial.ld",
])

config_setting(
    name = "hashed",
    flag_values = {
        ":hashed_flag": "True",
    },
)

config_setting(
    name = "type_static",
    flag_values = {
        ":type_flag": "static",
    },
)

config_setting(
    name = "type_binary_blob",
    flag_values = {
        ":type_flag": "binary_blob",
    },
)

config_setting(
    name = "crypto_fips_all",
    flag_values = {
        ":cryptolib_config_flag": "crypto_fips_all",
    },
)

# Indicate how crypto API should be compiled:
#    - static: using cc_library rule
#    - binary_blob: using opentitan_binary_blob rule which create a binary blob
#        and provide it in a byte array.
#    - relocatable: using opentitan_relocatable rule which create a relocatable
#        library.
string_flag(
    name = "type_flag",
    build_setting_default = "static",
    values = [
        "static",
        "binary_blob",
        "relocatable",
    ],
)

# Enable the self-integration check (hash) of the library.
# Note: not compatible with type_static
bool_flag(
    name = "hashed_flag",
    build_setting_default = False,
)

string_flag(
    name = "cryptolib_config_flag",
    build_setting_default = "crypto_dev",
    values = [
        "crypto_dev",
        "crypto_fips_all",
    ],
)
