# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def nist_cavp_repos():
    http_archive(
        name = "nist_cavp_ecdsa_fips_186_4",
        build_file = Label("//third_party/nist_cavp_testvectors:BUILD.nist_cavp_common.bazel"),
        strip_prefix = "186-4ecdsatestvectors",
        sha256 = "fe47cc92b4cee418236125c9ffbcd9bb01c8c34e74a4ba195d954bcb72824752",
        url = "https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/dss/186-4ecdsatestvectors.zip",
    )
