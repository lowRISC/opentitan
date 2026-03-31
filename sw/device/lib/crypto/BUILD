# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules/opentitan:defs.bzl", "OPENTITAN_CPU", "opentitan_binary_blob")
load("//rules/opentitan:static_library.bzl", "ot_static_library")
load("@rules_pkg//pkg:mappings.bzl", "pkg_files")
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")
load("//rules:linker.bzl", "ld_library")

cc_library(
    name = "otcrypto_api",
    copts = select({
        "//rules/configs:pic": [
            "-mcmodel=medany",
            "-mno-relax",
        ],
        "//conditions:default": ["-mcmodel=medlow"],
    }),
    defines =
        select({
            "//rules/configs:hashed": ["HASH_SELF_CHECK_ENABLE"],
            "//conditions:default": [],
        }),
    deps = [
        "//sw/device/lib/crypto/impl:aes",
        "//sw/device/lib/crypto/impl:aes_gcm",
        "//sw/device/lib/crypto/impl:drbg",
        "//sw/device/lib/crypto/impl:ecc_curve25519",
        "//sw/device/lib/crypto/impl:ecc_p256",
        "//sw/device/lib/crypto/impl:ecc_p384",
        "//sw/device/lib/crypto/impl:hkdf",
        "//sw/device/lib/crypto/impl:hmac",
        "//sw/device/lib/crypto/impl:kdf_ctr",
        "//sw/device/lib/crypto/impl:key_transport",
        "//sw/device/lib/crypto/impl:kmac",
        "//sw/device/lib/crypto/impl:kmac_kdf",
        "//sw/device/lib/crypto/impl:rsa",
        "//sw/device/lib/crypto/impl:security_config",
        "//sw/device/lib/crypto/impl:sha2",
        "//sw/device/lib/crypto/impl:sha3",
        "//sw/device/lib/crypto/impl:x25519",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

opentitan_binary_blob(
    name = "otcrypto_binary_blob_api",
    config = select({
        "//rules/configs:fips_all": "//rules/configs:fips_all.txt",
        "//conditions:default": None,
    }),
    deps_blob = [
        ":otcrypto_api",
        "//sw/device/lib/crypto/include:crypto_hdrs",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/runtime:log",
    ],
    # Public headers so generate_jump_table.py can parse them
    header = [
        "//sw/device/lib/crypto/include:aes.h",
        "//sw/device/lib/crypto/include:aes_gcm.h",
        "//sw/device/lib/crypto/include:drbg.h",
        "//sw/device/lib/crypto/include:ecc_curve25519.h",
        "//sw/device/lib/crypto/include:ecc_p256.h",
        "//sw/device/lib/crypto/include:ecc_p384.h",
        "//sw/device/lib/crypto/include:hkdf.h",
        "//sw/device/lib/crypto/include:hmac.h",
        "//sw/device/lib/crypto/include:kdf_ctr.h",
        "//sw/device/lib/crypto/include:key_transport.h",
        "//sw/device/lib/crypto/include:kmac.h",
        "//sw/device/lib/crypto/include:kmac_kdf.h",
        "//sw/device/lib/crypto/include:otcrypto.h",
        "//sw/device/lib/crypto/include:rsa.h",
        "//sw/device/lib/crypto/include:security_config.h",
        "//sw/device/lib/crypto/include:sha2.h",
        "//sw/device/lib/crypto/include:sha3.h",
        "//sw/device/lib/crypto/include:x25519.h",
    ],
    linkopts = select({
        "//rules/configs:pic": ["-mno-relax"],
        "//conditions:default": [],
    }),
    pic = select({
        "//rules/configs:pic": True,
        "//conditions:default": False,
    }),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/crypto/include:crypto_hdrs",
    ],
)

# Top-level cryptolib target.
ot_static_library(
    name = "otcrypto",
    deps = select({
        "//rules/configs:type_static": [":otcrypto_api"],
        "//rules/configs:type_binary_blob": [":otcrypto_binary_blob_api"],
        #"//rules/configs:type_relocatable": [":otcrypto_relocatable_api",],
        "//conditions:default": [],
    }),
)

# This library imports the archive created by the static library rule
# above. This can be used within the codebase to test the cryptolib
# as built.
cc_import(
    name = "crypto",
    static_library = ":otcrypto",
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/crypto/include:crypto_hdrs",
    ],
)

# This library imports the archive created by the static library rule
# above AND provides the header files as though they'd been exported
# from the repo in the same way as the packaged headers in the
# cryptolib.tar.xz output below.  This is used to create tests that
# verify the exported library and header files work correctly when
# exported.  Because we export a version of the `hardended_bool_t` and
# `status_t` types, it can be somewhat difficult to use this target
# within the repo (ie: you cannot use the in-repo definitions of those
# types, nor can you directly use anything that depends on those types).
# See //sw/device/test/crypto:otcrypto_export_test as an example.
cc_import(
    name = "crypto_exported_for_test",
    static_library = ":otcrypto",
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/crypto/include:exported_headers_for_test",
    ],
)

pkg_files(
    name = "package",
    srcs = [
        ":otcrypto",
    ],
    prefix = "crypto",
)

pkg_tar(
    name = "cryptolib",
    srcs = [
        ":package",
        "//sw/device/lib/crypto/include:package",
        "//sw/device/lib/crypto/include/freestanding:package",
    ],
    extension = "tar.xz",
)

filegroup(
    name = "otcrypto_binary_blob_elf",
    srcs = [":otcrypto_binary_blob_api"],
)

filegroup(
    name = "otcrypto_binary_blob_dis",
    srcs = [":otcrypto_binary_blob_api"],
)
