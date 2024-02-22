# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//rules:run_binary.bzl", "run_binary")

package(default_visibility = ["//visibility:public"])

run_binary(
    name = "nist_cavp_ecdsa_fips_186_4_sig_ver_json",
    srcs = [
        "//sw/host/cryptotest/testvectors/data/schemas:ecdsa_sig_ver_schema",
        "@nist_cavp_ecdsa_fips_186_4//:SigVer.rsp",
    ],
    outs = [":nist_cavp_ecdsa_fips_186_4_sig_ver.json"],
    args = [
        "--src",
        "$(location @nist_cavp_ecdsa_fips_186_4//:SigVer.rsp)",
        "--dst",
        "$(location :nist_cavp_ecdsa_fips_186_4_sig_ver.json)",
        "--schema",
        "$(location //sw/host/cryptotest/testvectors/data/schemas:ecdsa_sig_ver_schema)",
    ],
    tool = "//sw/host/cryptotest/testvectors/parsers:nist_cavp_ecdsa_parser",
)

[
    run_binary(
        name = cryptotest_name,
        srcs = [
            "@wycheproof//testvectors_v1:{}".format(src_name),
            "//sw/host/cryptotest/testvectors/data/schemas:ecdsa_sig_ver_schema",
        ],
        outs = [":{}.json".format(cryptotest_name)],
        args = [
            "--src",
            "$(location @wycheproof//testvectors_v1:{})".format(src_name),
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

[
    run_binary(
        name = cryptotest_name,
        srcs = [
            "@wycheproof//testvectors_v1:{}".format(src_name),
            "//sw/host/cryptotest/testvectors/data/schemas:kmac_schema.json",
        ],
        outs = [":{}.json".format(cryptotest_name)],
        args = [
            "--src",
            "$(location @wycheproof//testvectors_v1:{})".format(src_name),
            "--dst",
            "$(location :{}.json)".format(cryptotest_name),
            "--schema",
            "$(location //sw/host/cryptotest/testvectors/data/schemas:kmac_schema.json)",
            "--mode",
            mode,
        ],
        tool = "//sw/host/cryptotest/testvectors/parsers:wycheproof_kmac_parser",
    )
    for src_name, mode, cryptotest_name in [
        ("kmac128_no_customization_test.json", "128", "wycheproof_kmac_128"),
        ("kmac256_no_customization_test.json", "256", "wycheproof_kmac_256"),
    ]
]

[
    run_binary(
        name = "nist_cavp_aes_{}_{}_json".format(
            function_name.lower(),
            keylen_with_tmode,
        ),
        srcs = [
            "@nist_cavp_aes_kw_sp_800_38f//:{}_{}.txt".format(
                function_name,
                keylen_with_tmode,
            ),
            "//sw/host/cryptotest/testvectors/data/schemas:aes_kw_schema.json",
        ],
        outs = [":nist_cavp_aes_{}_{}.json".format(
            function_name.lower(),
            keylen_with_tmode,
        )],
        args = [
            "--src",
            "$(location @nist_cavp_aes_kw_sp_800_38f//:{}_{}.txt)".format(function_name, keylen_with_tmode),
            "--dst",
            "$(location :nist_cavp_aes_{}_{}.json)".format(
                function_name.lower(),
                keylen_with_tmode,
            ),
            "--operation",
            "{}".format(operation),
            "--key_len",
            "{}".format(key_len),
            "--padding",
            "{}".format(padding),
            "--transformation_mode",
            "{}".format(transformation_mode),
            "--schema",
            "$(location //sw/host/cryptotest/testvectors/data/schemas:aes_kw_schema.json)",
        ],
        tool = "//sw/host/cryptotest/testvectors/parsers:nist_cavp_aes_kw_parser",
    )
    for function_name, operation, padding in [
        ("KW_AD", "decrypt", False),
        ("KW_AE", "encrypt", False),
        ("KWP_AD", "decrypt", True),
        ("KWP_AE", "encrypt", True),
    ]
    for keylen_with_tmode, key_len, transformation_mode in [
        ("128_inv", "128", "inverse"),
        ("128", "128", "null"),
        ("192_inv", "192", "inverse"),
        ("192", "192", "null"),
        ("256_inv", "256", "inverse"),
        ("256", "256", "null"),
    ]
]

[
    run_binary(
        name = "nist_cavp_aes_{}_{}_json".format(
            function_name.lower(),
            key_len,
        ),
        srcs = [
            "@nist_cavp_aes_kw_sp_800_38f//:{}.txt".format(
                function_name,
            ),
            "//sw/host/cryptotest/testvectors/data/schemas:aes_kw_schema.json",
        ],
        outs = [":nist_cavp_aes_{}_{}.json".format(
            function_name.lower(),
            key_len,
        )],
        args = [
            "--src",
            "$(location @nist_cavp_aes_kw_sp_800_38f//:{}.txt)".format(function_name),
            "--dst",
            "$(location :nist_cavp_aes_{}_{}.json)".format(
                function_name.lower(),
                key_len,
            ),
            "--operation",
            "{}".format(operation),
            "--key_len",
            "{}".format(key_len),
            "--padding",
            "{}".format(padding),
            "--transformation_mode",
            "{}".format(transformation_mode),
            "--schema",
            "$(location //sw/host/cryptotest/testvectors/data/schemas:aes_kw_schema.json)",
        ],
        tool = "//sw/host/cryptotest/testvectors/parsers:nist_cavp_aes_kw_parser",
    )
    for function_name, key_len, operation, padding, transformation_mode in [
        ("TKW_AD", "192", "decrypt", False, "null"),
        ("TKW_AE", "192", "encrypt", False, "null"),
        ("TKW_AD_inv", "192", "decrypt", False, "inverse"),
        ("TKW_AE_inv", "192", "encrypt", False, "inverse"),
    ]
]

[
    run_binary(
        name = "nist_cavp_aes_gcm_{}_{}_json".format(
            ext_operation.lower(),
            key_len,
        ),
        srcs = [
            "@nist_cavp_aes_gcm//:gcm{}{}.rsp".format(ext_operation, key_len),
            "//sw/host/cryptotest/testvectors/data/schemas:aes_gcm_schema.json",
        ],
        outs = [":nist_gcm_{}_{}.json".format(
            operation.lower(),
            key_len,
        )],
        args = [
            "--src",
            "$(location @nist_cavp_aes_gcm//:gcm{}{}.rsp)".format(ext_operation, key_len),
            "--dst",
            "$(location :nist_gcm_{}_{}.json)".format(
                operation.lower(),
                key_len,
            ),
            "--operation",
            "{}".format(operation),
            "--key_len",
            "{}".format(key_len),
            "--schema",
            "$(location //sw/host/cryptotest/testvectors/data/schemas:aes_gcm_schema.json)",
        ],
        tool = "//sw/host/cryptotest/testvectors/parsers:nist_cavp_aes_gcm_parser",
    )
    for operation, ext_operation in [
        ("Decrypt", "Decrypt"),
        ("Encrypt", "EncryptExtIV"),
    ]
    for key_len in [
        "128",
        "192",
        "256",
    ]
]
