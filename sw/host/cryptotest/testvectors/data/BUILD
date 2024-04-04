# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//rules:run_binary.bzl", "run_binary")

package(default_visibility = ["//visibility:public"])

# Strip the inner layer of the DRBG repository, which is a zip of zips
genrule(
    name = "nist_cavp_drbg_sp_800_90a_reseed",
    srcs = ["@nist_cavp_drbg_sp_800_90a_root//:drbgvectors_pr_false.zip"],
    outs = [":CTR_DRBG_RESEED.rsp"],
    cmd = "unzip -p $(location @nist_cavp_drbg_sp_800_90a_root//:drbgvectors_pr_false.zip) CTR_DRBG.rsp > $(location :CTR_DRBG_RESEED.rsp)",
)

genrule(
    name = "nist_cavp_drbg_sp_800_90a_no_reseed",
    srcs = ["@nist_cavp_drbg_sp_800_90a_root//:drbgvectors_no_reseed.zip"],
    outs = [":CTR_DRBG_NO_RESEED.rsp"],
    cmd = "unzip -p $(location @nist_cavp_drbg_sp_800_90a_root//:drbgvectors_no_reseed.zip) CTR_DRBG.rsp > $(location :CTR_DRBG_NO_RESEED.rsp)",
)

[
    run_binary(
        name = "nist_cavp_drbg_sp_800_90a_{}_json".format(mode),
        srcs = [
            ":CTR_DRBG_{}.rsp".format(mode.upper()),
            "//sw/host/cryptotest/testvectors/data/schemas:drbg_schema.json",
        ],
        outs = [":nist_cavp_drbg_sp_800_90a_{}.json".format(mode)],
        args = [
            "--src",
            "$(location :CTR_DRBG_{}.rsp)".format(mode.upper()),
            "--dst",
            "$(location :nist_cavp_drbg_sp_800_90a_{}.json)".format(mode),
            "--schema",
            "$(location //sw/host/cryptotest/testvectors/data/schemas:drbg_schema.json)",
        ] + (["--reseed"] if reseed else []),
        tool = "//sw/host/cryptotest/testvectors/parsers:nist_cavp_drbg_parser",
    )
    for mode, reseed in [
        ("reseed", True),
        ("no_reseed", False),
    ]
]

run_binary(
    name = "nist_cavp_ecdsa_fips_186_4_sig_ver_json",
    srcs = [
        "//sw/host/cryptotest/testvectors/data/schemas:ecdsa_schema",
        "@nist_cavp_ecdsa_fips_186_4//:SigVer.rsp",
    ],
    outs = [":nist_cavp_ecdsa_fips_186_4_sig_ver.json"],
    args = [
        "--src",
        "$(location @nist_cavp_ecdsa_fips_186_4//:SigVer.rsp)",
        "--dst",
        "$(location :nist_cavp_ecdsa_fips_186_4_sig_ver.json)",
        "--schema",
        "$(location //sw/host/cryptotest/testvectors/data/schemas:ecdsa_schema)",
        "--operation",
        "verify",
    ],
    tool = "//sw/host/cryptotest/testvectors/parsers:nist_cavp_ecdsa_parser",
)

run_binary(
    name = "nist_cavp_ecdsa_fips_186_4_sign_json",
    srcs = [
        "//sw/host/cryptotest/testvectors/data/schemas:ecdsa_schema",
        # We use the .txt test vector file here, because the .rsp one does not
        # include the private keys.
        "@nist_cavp_ecdsa_fips_186_4//:SigGen.txt",
    ],
    outs = ["nist_cavp_ecdsa_fips_186_4_sign.json"],
    args = [
        "--src",
        "$(location @nist_cavp_ecdsa_fips_186_4//:SigGen.txt)",
        "--dst",
        "$(location :nist_cavp_ecdsa_fips_186_4_sign.json)",
        "--schema",
        "$(location //sw/host/cryptotest/testvectors/data/schemas:ecdsa_schema)",
        "--operation",
        "sign",
    ],
    tool = "//sw/host/cryptotest/testvectors/parsers:nist_cavp_ecdsa_parser",
)

[
    run_binary(
        name = cryptotest_name,
        srcs = [
            "@wycheproof//testvectors_v1:{}".format(src_name),
            "//sw/host/cryptotest/testvectors/data/schemas:ecdsa_schema",
        ],
        outs = [":{}.json".format(cryptotest_name)],
        args = [
            "--src",
            "$(location @wycheproof//testvectors_v1:{})".format(src_name),
            "--dst",
            "$(location :{}.json)".format(cryptotest_name),
            "--schema",
            "$(location //sw/host/cryptotest/testvectors/data/schemas:ecdsa_schema)",
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

run_binary(
    name = "nist_cavp_ecdh_sp_800_56a_json",
    srcs = [
        "//sw/host/cryptotest/testvectors/data/schemas:ecdh_schema.json",
        "@nist_cavp_ecdh_sp_800_56a//:KAS_ECC_CDH_PrimitiveTest.txt",
    ],
    outs = [":nist_cavp_ecdh_sp_800_56a.json"],
    args = [
        "--src",
        "$(location @nist_cavp_ecdh_sp_800_56a//:KAS_ECC_CDH_PrimitiveTest.txt)",
        "--dst",
        "$(location :nist_cavp_ecdh_sp_800_56a.json)",
        "--schema",
        "$(location //sw/host/cryptotest/testvectors/data/schemas:ecdh_schema.json)",
    ],
    tool = "//sw/host/cryptotest/testvectors/parsers:nist_cavp_ecdh_parser",
)

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

run_binary(
    name = "nist_cavp_hmac_fips_198_1_json",
    srcs = [
        "//sw/host/cryptotest/testvectors/data/schemas:hmac_schema.json",
        "@nist_cavp_hmac_fips_198_1//:HMAC.rsp",
    ],
    outs = ["nist_cavp_hmac_fips_198_1.json"],
    args = [
        "--src",
        "$(location @nist_cavp_hmac_fips_198_1//:HMAC.rsp)",
        "--dst",
        "$(location :nist_cavp_hmac_fips_198_1.json)",
        "--schema",
        "$(location //sw/host/cryptotest/testvectors/data/schemas:hmac_schema.json)",
    ],
    tool = "//sw/host/cryptotest/testvectors/parsers:nist_cavp_hmac_parser",
)

run_binary(
    name = "hjson_hash",
    srcs = [
        "//sw/device/tests/crypto/testvectors:hash_hardcoded.hjson",
        "//sw/host/cryptotest/testvectors/data/schemas:hash_schema.json",
    ],
    outs = [":hjson_hash.json"],
    args = [
        "--src",
        "$(location //sw/device/tests/crypto/testvectors:hash_hardcoded.hjson)",
        "--dst",
        "$(location :hjson_hash.json)",
        "--schema",
        "$(location //sw/host/cryptotest/testvectors/data/schemas:hash_schema.json)",
    ],
    tool = "//sw/host/cryptotest/testvectors/parsers:hjson_hash_parser",
)

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
        name = cryptotest_name,
        srcs = [
            "@wycheproof//testvectors_v1:{}".format(src_name),
            "//sw/host/cryptotest/testvectors/data/schemas:hmac_schema.json",
        ],
        outs = [":{}.json".format(cryptotest_name)],
        args = [
            "--src",
            "$(location @wycheproof//testvectors_v1:{})".format(src_name),
            "--dst",
            "$(location :{}.json)".format(cryptotest_name),
            "--schema",
            "$(location //sw/host/cryptotest/testvectors/data/schemas:hmac_schema.json)",
            "--hash",
            hash_alg,
        ],
        tool = "//sw/host/cryptotest/testvectors/parsers:wycheproof_hmac_parser",
    )
    for src_name, hash_alg, cryptotest_name in [
        ("hmac_sha256_test.json", "sha-256", "wycheproof_hmac_sha256"),
        ("hmac_sha384_test.json", "sha-384", "wycheproof_hmac_sha384"),
        ("hmac_sha512_test.json", "sha-512", "wycheproof_hmac_sha512"),
        ("hmac_sha3_256_test.json", "sha3-256", "wycheproof_hmac_sha3_256"),
        ("hmac_sha3_384_test.json", "sha3-384", "wycheproof_hmac_sha3_384"),
        ("hmac_sha3_512_test.json", "sha3-512", "wycheproof_hmac_sha3_512"),
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

[
    run_binary(
        name = "nist_cavp_rsa_{}_{}_json".format(
            padding_mode,
            operation,
        ),
        srcs = [
            "@nist_cavp_rsa_fips_186_3//:Sig{}{}_186-3.{}".format(prefix, infix, suffix),
            "//sw/host/cryptotest/testvectors/data/schemas:rsa_schema.json",
        ],
        outs = [":nist_rsa_{}_{}.json".format(
            padding_mode,
            operation,
        )],
        args = [
            "--src",
            "$(location @nist_cavp_rsa_fips_186_3//:Sig{}{}_186-3.{})".format(prefix, infix, suffix),
            "--dst",
            "$(location :nist_rsa_{}_{}.json)".format(
                padding_mode,
                operation,
            ),
            "--schema",
            "$(location //sw/host/cryptotest/testvectors/data/schemas:rsa_schema.json)",
            "--operation",
            operation,
            "--padding",
            padding_mode,
        ],
        tool = "//sw/host/cryptotest/testvectors/parsers:nist_cavp_rsa_parser",
    )
    for padding_mode, infix in [
        ("pkcs1_1.5", "15"),
        ("pss", "PSS"),
    ]
    for operation, prefix, suffix in [
        ("sign", "Gen", "txt"),
        ("verify", "Ver", "rsp"),
    ]
]

run_binary(
    name = "rsp_sphincsplus_shake256_128s_simple_json",
    srcs = [
        "//sw/host/cryptotest/testvectors/data/schemas:sphincsplus_schema.json",
        "@sphincsplus_kat//:sphincs-shake256-128s-simple/PQCsignKAT_64.rsp",
    ],
    outs = [":rsp_sphincsplus_shake256_128s_simple.json"],
    args = [
        "--src",
        "$(location @sphincsplus_kat//:sphincs-shake256-128s-simple/PQCsignKAT_64.rsp)",
        "--dst",
        "$(location :rsp_sphincsplus_shake256_128s_simple.json)",
        "--schema",
        "$(location //sw/host/cryptotest/testvectors/data/schemas:sphincsplus_schema.json)",
        "--hash_alg",
        "shake-256",
    ],
    tool = "//sw/host/cryptotest/testvectors/parsers:rsp_sphincsplus_parser",
)

run_binary(
    name = "hjson_kmac",
    srcs = [
        "//sw/device/tests/crypto/testvectors:kmac_hardcoded.hjson",
        "//sw/host/cryptotest/testvectors/data/schemas:kmac_schema.json",
    ],
    outs = [":hjson_kmac.json"],
    args = [
        "--src",
        "$(location //sw/device/tests/crypto/testvectors:kmac_hardcoded.hjson)",
        "--dst",
        "$(location :hjson_kmac.json)",
        "--schema",
        "$(location //sw/host/cryptotest/testvectors/data/schemas:kmac_schema.json)",
    ],
    tool = "//sw/host/cryptotest/testvectors/parsers:hjson_kmac_parser",
)
