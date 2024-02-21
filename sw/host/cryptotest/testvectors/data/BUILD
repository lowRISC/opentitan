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
            "@wycheproof//testvectors:{}".format(src_name),
            "//sw/host/cryptotest/testvectors/data/schemas:ecdsa_sig_ver_schema",
        ],
        outs = [":{}.json".format(cryptotest_name)],
        args = [
            "--src",
            "$(location @wycheproof//testvectors:{})".format(src_name),
            "--dst",
            "$(location :{}.json)".format(cryptotest_name),
            "--schema",
            "$(location //sw/host/cryptotest/testvectors/data/schemas:ecdsa_sig_ver_schema)",
        ],
        tool = "//sw/host/cryptotest/testvectors/parsers:wycheproof_ecdsa_parser",
    )
    for src_name, cryptotest_name in [
        ("ecdsa_secp256r1_sha256_test.json", "wycheproof_ecdsa_p256_sha256"),
        ("ecdsa_secp256r1_sha512_test.json", "wycheproof_ecdsa_p256_sha512"),
        ("ecdsa_secp256r1_sha3_256_test.json", "wycheproof_ecdsa_p256_sha3_256"),
        ("ecdsa_secp256r1_sha3_512_test.json", "wycheproof_ecdsa_p256_sha3_512"),
        ("ecdsa_secp384r1_sha384_test.json", "wycheproof_ecdsa_p384_sha384"),
        ("ecdsa_secp384r1_sha512_test.json", "wycheproof_ecdsa_p384_sha512"),
        ("ecdsa_secp384r1_sha3_384_test.json", "wycheproof_ecdsa_p384_sha3_384"),
        ("ecdsa_secp384r1_sha3_512_test.json", "wycheproof_ecdsa_p384_sha3_512"),
    ]
]

[
    run_binary(
        name = "nist_cavp_{}_{}_{}_json".format(
            src_repo,
            algorithm.lower(),
            msg_type.lower(),
        ),
        srcs = [
            "@nist_cavp_{}//:{}{}.rsp".format(src_repo, algorithm, msg_type),
            "//sw/host/cryptotest/testvectors/data/schemas:hash_schema.json",
        ],
        outs = [":nist_{}_{}.json".format(
            algorithm.lower(),
            msg_type.lower(),
        )],
        args = [
            "--src",
            "$(location @nist_cavp_{}//:{}{}.rsp)".format(src_repo, algorithm, msg_type),
            "--dst",
            "$(location :nist_{}_{}.json)".format(
                algorithm.lower(),
                msg_type.lower(),
            ),
            "--schema",
            "$(location //sw/host/cryptotest/testvectors/data/schemas:hash_schema.json)",
            "--algorithm",
            algorithm,
        ],
        tool = "//sw/host/cryptotest/testvectors/parsers:nist_cavp_hash_parser",
    )
    for algorithm, src_repo, extra_msg_types in [
        ("SHA256", "sha2_fips_180_4", []),
        ("SHA384", "sha2_fips_180_4", []),
        ("SHA512", "sha2_fips_180_4", []),
        ("SHA3_256", "sha3_fips_202", []),
        ("SHA3_384", "sha3_fips_202", []),
        ("SHA3_512", "sha3_fips_202", []),
        (
            "SHAKE128",
            "shake_fips_202",
            ["VariableOut"],
        ),
        (
            "SHAKE256",
            "shake_fips_202",
            ["VariableOut"],
        ),
    ]
    for msg_type in [
        "ShortMsg",
        "LongMsg",
    ] + extra_msg_types
]

[
    run_binary(
        name = cryptotest_name,
        srcs = [
            "@wycheproof//testvectors_v1:{}".format(src_name),
            "//sw/host/cryptotest/testvectors/data/schemas:ecdh_schema.json",
        ],
        outs = [":{}.json".format(cryptotest_name)],
        args = [
            "--src",
            "$(location @wycheproof//testvectors_v1:{})".format(src_name),
            "--dst",
            "$(location :{}.json)".format(cryptotest_name),
            "--schema",
            "$(location //sw/host/cryptotest/testvectors/data/schemas:ecdh_schema.json)",
        ],
        tool = "//sw/host/cryptotest/testvectors/parsers:wycheproof_ecdh_parser",
    )
    for src_name, cryptotest_name in [
        ("ecdh_secp256r1_test.json", "wycheproof_ecdh_p256"),
        ("ecdh_secp384r1_test.json", "wycheproof_ecdh_p384"),
    ]
]
