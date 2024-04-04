# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(":cryptotest.bzl", "cryptotest")

package(default_visibility = ["//visibility:public"])

AES_TESTVECTOR_TARGETS = [
    "//sw/host/cryptotest/testvectors/data/aes_nist_kat:{}_{}_{}_json".format(alg, kat_type, key_len)
    for alg in ("cbc", "cfb128", "ecb", "ofb")
    for kat_type in ("varkey", "gfsbox", "vartxt", "keysbox")
    for key_len in ("128", "192", "256")
]

AES_TESTVECTOR_ARGS = " ".join([
    "--aes-json=\"$(rootpath {})\"".format(target)
    for target in AES_TESTVECTOR_TARGETS
])

cryptotest(
    name = "aes_kat",
    test_args = AES_TESTVECTOR_ARGS,
    test_harness = "//sw/host/tests/crypto/aes_nist_kat:harness",
    test_vectors = AES_TESTVECTOR_TARGETS,
)

ECDSA_TESTVECTOR_TARGETS = [
    "//sw/host/cryptotest/testvectors/data:wycheproof_ecdsa_{}.json".format(config)
    for config in [
        "p256_sha256",
        "p256_sha512",
        "p256_sha3_256",
        "p256_sha3_512",
        # TODO uncomment when cryptolib supports ECDSA with P-384
        # "p384_sha384",
        # "p384_sha512",
        # "p384_sha3_384",
        # "p384_sha3_512",
    ]
] + [
    "//sw/host/cryptotest/testvectors/data:nist_cavp_ecdsa_fips_186_4_sig_ver_json",
    "//sw/host/cryptotest/testvectors/data:nist_cavp_ecdsa_fips_186_4_sign_json",
]

ECDSA_TESTVECTOR_ARGS = " ".join([
    "--ecdsa-json=\"$(rootpath {})\"".format(target)
    for target in ECDSA_TESTVECTOR_TARGETS
])

cryptotest(
    name = "ecdsa_kat",
    test_args = ECDSA_TESTVECTOR_ARGS,
    test_harness = "//sw/host/tests/crypto/ecdsa_kat:harness",
    test_vectors = ECDSA_TESTVECTOR_TARGETS,
)

ECDH_TESTVECTOR_TARGETS = [
    "//sw/host/cryptotest/testvectors/data:wycheproof_ecdh_{}".format(mode)
    for mode in [
        "p256",
        # TODO uncomment when ECDH supports P-384
        # "p384",
    ]
] + [
    "//sw/host/cryptotest/testvectors/data:nist_cavp_ecdh_sp_800_56a_json",
]

ECDH_TESTVECTOR_ARGS = " ".join([
    "--ecdh-json=\"$(rootpath {})\"".format(target)
    for target in ECDH_TESTVECTOR_TARGETS
])

cryptotest(
    name = "ecdh_kat",
    test_args = ECDH_TESTVECTOR_ARGS,
    test_harness = "//sw/host/tests/crypto/ecdh_kat:harness",
    test_vectors = ECDH_TESTVECTOR_TARGETS,
)

HASH_TESTVECTOR_TARGETS = [
    "//sw/host/cryptotest/testvectors/data:nist_cavp_{}_{}_{}_json".format(
        src_repo,
        algorithm.lower(),
        msg_type.lower(),
    )
    for algorithm, src_repo, extra_msg_types in [
        #        ("SHA256", "sha2_fips_180_4", []),
        #        ("SHA384", "sha2_fips_180_4", []),
        #        ("SHA512", "sha2_fips_180_4", []),
        #        ("SHA3_256", "sha3_fips_202", []),
        #        ("SHA3_384", "sha3_fips_202", []),
        #        ("SHA3_512", "sha3_fips_202", []),
        #        (
        #            "SHAKE128",
        #            "shake_fips_202",
        #            ["VariableOut"],
        #        ),
        #        (
        #            "SHAKE256",
        #            "shake_fips_202",
        #            ["VariableOut"],
        #        ),
    ]
    for msg_type in [
        "ShortMsg",
        "LongMsg",
    ] + extra_msg_types
] + [
    "//sw/host/cryptotest/testvectors/data:hjson_hash",
]

HASH_TESTVECTOR_ARGS = " ".join([
    "--hash-json=\"$(rootpath {})\"".format(target)
    for target in HASH_TESTVECTOR_TARGETS
])

cryptotest(
    name = "hash_kat",
    test_args = HASH_TESTVECTOR_ARGS,
    test_harness = "//sw/host/tests/crypto/hash_kat:harness",
    test_vectors = HASH_TESTVECTOR_TARGETS,
)

DRBG_TESTVECTOR_TARGETS = [
    "//sw/host/cryptotest/testvectors/data:nist_cavp_drbg_sp_800_90a_reseed_json",
    "//sw/host/cryptotest/testvectors/data:nist_cavp_drbg_sp_800_90a_no_reseed_json",
]

DRBG_TESTVECTOR_ARGS = " ".join([
    "--drbg-json=\"$(rootpath {})\"".format(target)
    for target in DRBG_TESTVECTOR_TARGETS
])

cryptotest(
    name = "drbg_kat",
    test_args = DRBG_TESTVECTOR_ARGS,
    test_harness = "//sw/host/tests/crypto/drbg_kat:harness",
    test_vectors = DRBG_TESTVECTOR_TARGETS,
)

HMAC_TESTVECTOR_TARGETS = [
    "//sw/host/cryptotest/testvectors/data:wycheproof_hmac_{}.json".format(config)
    for config in [
        "sha256",
        "sha384",
        "sha512",
        # TODO uncomment when cryptolib supports HMAC with SHA3
        # "sha3_256",
        # "sha3_512",
    ]
] + [
    "//sw/host/cryptotest/testvectors/data:nist_cavp_hmac_fips_198_1_json",
]

HMAC_TESTVECTOR_ARGS = " ".join([
    "--hmac-json=\"$(rootpath {})\"".format(target)
    for target in HMAC_TESTVECTOR_TARGETS
])

cryptotest(
    name = "hmac_kat",
    test_args = HMAC_TESTVECTOR_ARGS,
    test_harness = "//sw/host/tests/crypto/hmac_kat:harness",
    test_vectors = HMAC_TESTVECTOR_TARGETS,
)

KMAC_TESTVECTOR_TARGETS = [
    "//sw/host/cryptotest/testvectors/data:wycheproof_kmac_{}.json".format(config)
    for config in [
        "128",
        "256",
    ]
]

KMAC_TESTVECTOR_ARGS = " ".join([
    "--kmac-json=\"$(rootpath {})\"".format(target)
    for target in KMAC_TESTVECTOR_TARGETS
])

cryptotest(
    name = "kmac_kat",
    test_args = KMAC_TESTVECTOR_ARGS,
    test_harness = "//sw/host/tests/crypto/kmac_kat:harness",
    test_vectors = KMAC_TESTVECTOR_TARGETS,
)

# Use the following command to run the entire test suite in a given target:
# $ export OT_EXEC_ENV=silicon_owner_sival_rom_ext
# $ bazel test --//signing:token=//signing/tokens:cloud_kms \
#    --cache_test_results=no --test_output=errors --local_test_jobs=1 \
#    --build_tag_filters=${OT_EXEC_ENV} \
#    --test_tag_filters=${OT_EXEC_ENV}  \
#    --test_output=errors \
#     //sw/device/tests/crypto/cryptotest:crypto_kat_test_suite
test_suite(
    name = "crypto_kat_test_suite",
    tests = [
        ":aes_kat",
        ":drbg_kat",
        ":ecdh_kat",
        ":ecdsa_kat",
        ":hash_kat",
        ":hmac_kat",
        ":kmac_kat",
    ],
)
