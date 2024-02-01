# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def sphincsplus_repos():
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
