# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:repo.bzl", "http_archive_or_local")
load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def sphincsplus_repos(local = None):
    http_archive(
        name = "sphincsplus_kat",
        build_file = Label("//third_party/sphincsplus:BUILD.sphincsplus_common.bazel"),
        strip_prefix = "NIST-PQ-Submission-SPHINCS-20201001/KAT",
        sha256 = "798c9ef5a851cd92e52e6c2fcc8403530a5f827bf07bf542e3dfdf98c1916338",
        urls = [
            # Self-hosted GCB ZIP that contains only the 128s/SHAKE256 test
            # vectors. The original archive hosted at
            # https://sphincs.org/data/sphincs+-round3-submission-nist.zip
            # which includes the test vectors for all versions is not included
            # here because the checksum differs.
            "https://storage.googleapis.com/ot-crypto-test-vectors/sphincsplus/sphincsplus_shake256_128s_round3.zip ",
        ],
    )
    http_archive_or_local(
        name = "sphincsplus_fips205_ipd",
        local = local,
        url = "https://github.com/sphincs/sphincsplus/archive/129b72c80e122a22a61f71b5d2b042770890ccee.tar.gz",
        strip_prefix = "sphincsplus-129b72c80e122a22a61f71b5d2b042770890ccee/ref",
        build_file = "//third_party/sphincsplus:BUILD.sphincsplus.bazel",
        sha256 = "b301faa7a42ef538323a732929d49341b1cbd8375f643f7d98ca32cd6efacc32",
    )
