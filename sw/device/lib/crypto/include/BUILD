# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("@rules_pkg//pkg:mappings.bzl", "pkg_files")

config_setting(
    name = "disable_buf_integrity_checks",
    define_values = {
        "disable_buf_integrity_checks": "true",
    },
)

# Export all headers.
exports_files(glob(["*.h"]))

cc_library(
    name = "datatypes",
    hdrs = ["datatypes.h"],
    defines = ["OTCRYPTO_IN_REPO=1"] + select({
        ":disable_buf_integrity_checks": ["OTCRYPTO_DISABLE_BUF_INTEGRITY_CHECKS"],
        "//conditions:default": [],
    }),
    includes = ["."],
    deps = [
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:status",
    ],
)

cc_library(
    name = "crypto_hdrs",
    hdrs = [
        "aes.h",
        "aes_gcm.h",
        "config.h",
        "cryptolib_build_info.h",
        "datatypes.h",
        "drbg.h",
        "ecc_curve25519.h",
        "ecc_p256.h",
        "ecc_p384.h",
        "entropy_src.h",
        "hkdf.h",
        "hmac.h",
        "integrity.h",
        "kdf_ctr.h",
        "key_transport.h",
        "kmac.h",
        "kmac_kdf.h",
        "otcrypto.h",
        "rsa.h",
        "sha2.h",
        "sha3.h",
    ],
    defines = ["OTCRYPTO_IN_REPO=1"] + select({
        ":disable_buf_integrity_checks": ["OTCRYPTO_DISABLE_BUF_INTEGRITY_CHECKS"],
        "//conditions:default": [],
    }),
    includes = ["."],
    deps = [
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:status",
    ],
)

# Create a library that makes the headers available as though we've been
# exported from the repo (ie: OTCRYPTO_IN_REPO is not set).
cc_library(
    name = "exported_headers_for_test",
    hdrs = [
        "aes.h",
        "aes_gcm.h",
        "config.h",
        "cryptolib_build_info.h",
        "datatypes.h",
        "drbg.h",
        "ecc_curve25519.h",
        "ecc_p256.h",
        "ecc_p384.h",
        "entropy_src.h",
        "hkdf.h",
        "hmac.h",
        "integrity.h",
        "kdf_ctr.h",
        "key_transport.h",
        "kmac.h",
        "kmac_kdf.h",
        "otcrypto.h",
        "rsa.h",
        "sha2.h",
        "sha3.h",
        "//sw/device/lib/crypto/include/freestanding:absl_status.h",
        "//sw/device/lib/crypto/include/freestanding:defs.h",
        "//sw/device/lib/crypto/include/freestanding:hardened.h",
    ],
    includes = ["."],
)

pkg_files(
    name = "package",
    srcs = glob(["*.h"]),
    prefix = "crypto/include",
)

genrule(
    name = "doxygen",
    srcs = glob(["*.h"]),
    outs = [
        "Doxyfile",
        "latex/refman.pdf",
    ],
    cmd = """
        GIT_COMMIT=$$(grep STABLE_BUILD_SCM_REVISION bazel-out/stable-status.txt | cut -d' ' -f2 || echo "unknown")

        DOXY_VERSION="$${GIT_COMMIT}"

        cat <<EOF > $(location Doxyfile)
PROJECT_NAME="Cryptolib API User Guidance"
PROJECT_NUMBER="version: $${DOXY_VERSION}"
OUTPUT_DIRECTORY="$(RULEDIR)"
HAVE_DOT=NO
OPTIMIZE_OUTPUT_FOR_C=YES
LATEX_HIDE_INDICES=YES
EOF

        for f in $(SRCS); do
            echo "INPUT+=$$f" >> $(location Doxyfile)
        done

        doxygen $(location Doxyfile)
        make -C $(RULEDIR)/latex
    """,
    # Tell Bazel we want to version this
    stamp = 1,
)
