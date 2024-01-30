# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//rules:run_binary.bzl", "run_binary")

package(default_visibility = ["//visibility:public"])

genrule(
    name = "nist_cavp_ecdsa_fips_186_4_sig_ver_json",
    srcs = [
        "@nist_cavp_ecdsa_fips_186_4//:SigVer.rsp",
        "//sw/host/cryptotest/testvectors/data/schemas:ecdsa_sig_ver_schema",
    ],
    outs = ["nist_cavp_ecdsa_fips_186_4_sig_ver.json"],
    cmd = """$(location //sw/host/cryptotest/testvectors/parsers:nist_cavp_ecdsa_parser) \
            --src $(location @nist_cavp_ecdsa_fips_186_4//:SigVer.rsp) \
            --dst $(RULEDIR)/nist_cavp_ecdsa_fips_186_4_sig_ver \
            --schema $(location //sw/host/cryptotest/testvectors/data/schemas:ecdsa_sig_ver_schema)""",
    message = "Parsing testvector - NIST CAVP Digital Signatures FIPS 186-4 - ECDSA",
    tools = ["//sw/host/cryptotest/testvectors/parsers:nist_cavp_ecdsa_parser"],
)

[
    run_binary(
        name = cryptotest_name,
        srcs = [
            "//sw/vendor/wycheproof/testvectors:{}".format(src_name),
            "//sw/host/cryptotest/testvectors/data/schemas:ecdsa_sig_ver_schema",
        ],
        outs = [":{}.json".format(cryptotest_name)],
        args = [
            "--src",
            "$(location //sw/vendor/wycheproof/testvectors:{})".format(src_name),
            "--dst",
            "$(location :{}.json)".format(cryptotest_name),
            "--schema",
            "$(location //sw/host/cryptotest/testvectors/data/schemas:ecdsa_sig_ver_schema)",
        ],
        tool = "//sw/host/cryptotest/testvectors/parsers:wycheproof_ecdsa_parser",
    )
    for src_name, cryptotest_name in [
        ("ecdsa_secp256r1_sha256_test.json", "wycheproof_ecdsa_p256_sha256"),
        ("ecdsa_secp384r1_sha384_test.json", "wycheproof_ecdsa_p384_sha384"),
    ]
]
