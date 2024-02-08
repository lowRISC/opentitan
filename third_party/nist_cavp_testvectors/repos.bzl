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
    http_archive(
        name = "nist_cavp_sha2_fips_180_4",
        build_file = Label("//third_party/nist_cavp_testvectors:BUILD.nist_cavp_common.bazel"),
        strip_prefix = "shabytetestvectors",
        sha256 = "929ef80b7b3418aca026643f6f248815913b60e01741a44bba9e118067f4c9b8",
        url = "https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/shs/shabytetestvectors.zip",
    )
    http_archive(
        name = "nist_cavp_sha3_fips_202",
        build_file = Label("//third_party/nist_cavp_testvectors:BUILD.nist_cavp_common.bazel"),
        sha256 = "cd07701af2e47f5cc889d642528b4bf11f8b6eb55797c7307a96828ed8d8fc8c",
        url = "https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/sha3/sha-3bytetestvectors.zip",
    )
    http_archive(
        name = "nist_cavp_shake_fips_202",
        build_file = Label("//third_party/nist_cavp_testvectors:BUILD.nist_cavp_common.bazel"),
        sha256 = "debfebc3157b3ceea002b84ca38476420389a3bf7e97dc5f53ea4689a16de4c7",
        url = "https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/sha3/shakebytetestvectors.zip",
    )
