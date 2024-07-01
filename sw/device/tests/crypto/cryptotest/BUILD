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
] + [
    "//sw/host/cryptotest/testvectors/data:random_ecdsa_{}".format(random_target)
    for random_target in [
        "p256_sha256",
        "p256_sha384",
        "p256_sha512",
        "p256_sha3_256",
        "p256_sha3_384",
        "p256_sha3_512",
        # TODO uncomment when cryptolib supports ECDSA with P-384
        # "p384_sha256",
        # "p384_sha384",
        # "p384_sha512",
        # "p384_sha3_256",
        # "p384_sha3_384",
        # "p384_sha3_512",
    ]
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

SHA256_TESTVECTOR_TARGETS = [
    "//sw/host/cryptotest/testvectors/data:nist_cavp_sha2_fips_180_4_sha256_{}_json".format(
        msg_type.lower(),
    )
    for msg_type in [
        "ShortMsg",
        "LongMsg",
    ]
]

SHA256_TESTVECTOR_ARGS = " ".join([
    "--hash-json=\"$(rootpath {})\"".format(target)
    for target in SHA256_TESTVECTOR_TARGETS
])

cryptotest(
    name = "sha256_kat",
    test_args = SHA256_TESTVECTOR_ARGS,
    test_harness = "//sw/host/tests/crypto/hash_kat:harness",
    test_vectors = SHA256_TESTVECTOR_TARGETS,
)

SHA384_TESTVECTOR_TARGETS = [
    "//sw/host/cryptotest/testvectors/data:nist_cavp_sha2_fips_180_4_sha384_{}_json".format(
        msg_type.lower(),
    )
    for msg_type in [
        "ShortMsg",
        "LongMsg",
    ]
]

SHA384_TESTVECTOR_ARGS = " ".join([
    "--hash-json=\"$(rootpath {})\"".format(target)
    for target in SHA384_TESTVECTOR_TARGETS
])

cryptotest(
    name = "sha384_kat",
    test_args = SHA384_TESTVECTOR_ARGS,
    test_harness = "//sw/host/tests/crypto/hash_kat:harness",
    test_vectors = SHA384_TESTVECTOR_TARGETS,
)

SHA512_TESTVECTOR_TARGETS = [
    "//sw/host/cryptotest/testvectors/data:nist_cavp_sha2_fips_180_4_sha512_{}_json".format(
        msg_type.lower(),
    )
    for msg_type in [
        "ShortMsg",
        "LongMsg",
    ]
]

SHA512_TESTVECTOR_ARGS = " ".join([
    "--hash-json=\"$(rootpath {})\"".format(target)
    for target in SHA512_TESTVECTOR_TARGETS
])

cryptotest(
    name = "sha512_kat",
    test_args = SHA512_TESTVECTOR_ARGS,
    test_harness = "//sw/host/tests/crypto/hash_kat:harness",
    test_vectors = SHA512_TESTVECTOR_TARGETS,
)

SHA3_256_TESTVECTOR_TARGETS = [
    "//sw/host/cryptotest/testvectors/data:nist_cavp_sha3_fips_202_sha3_256_{}_json".format(
        msg_type.lower(),
    )
    for msg_type in [
        "ShortMsg",
        "LongMsg",
    ]
]

SHA3_256_TESTVECTOR_ARGS = " ".join([
    "--hash-json=\"$(rootpath {})\"".format(target)
    for target in SHA3_256_TESTVECTOR_TARGETS
])

cryptotest(
    name = "sha3_256_kat",
    test_args = SHA3_256_TESTVECTOR_ARGS,
    test_harness = "//sw/host/tests/crypto/hash_kat:harness",
    test_vectors = SHA3_256_TESTVECTOR_TARGETS,
)

SHA3_384_TESTVECTOR_TARGETS = [
    "//sw/host/cryptotest/testvectors/data:nist_cavp_sha3_fips_202_sha3_384_{}_json".format(
        msg_type.lower(),
    )
    for msg_type in [
        "ShortMsg",
        "LongMsg",
    ]
]

SHA3_384_TESTVECTOR_ARGS = " ".join([
    "--hash-json=\"$(rootpath {})\"".format(target)
    for target in SHA3_384_TESTVECTOR_TARGETS
])

cryptotest(
    name = "sha3_384_kat",
    test_args = SHA3_384_TESTVECTOR_ARGS,
    test_harness = "//sw/host/tests/crypto/hash_kat:harness",
    test_vectors = SHA3_384_TESTVECTOR_TARGETS,
)

SHA3_512_TESTVECTOR_TARGETS = [
    "//sw/host/cryptotest/testvectors/data:nist_cavp_sha3_fips_202_sha3_512_{}_json".format(
        msg_type.lower(),
    )
    for msg_type in [
        "ShortMsg",
        "LongMsg",
    ]
]

SHA3_512_TESTVECTOR_ARGS = " ".join([
    "--hash-json=\"$(rootpath {})\"".format(target)
    for target in SHA3_512_TESTVECTOR_TARGETS
])

cryptotest(
    name = "sha3_512_kat",
    test_args = SHA3_512_TESTVECTOR_ARGS,
    test_harness = "//sw/host/tests/crypto/hash_kat:harness",
    test_vectors = SHA3_512_TESTVECTOR_TARGETS,
)

SHAKE128_TESTVECTOR_TARGETS = [
    "//sw/host/cryptotest/testvectors/data:nist_cavp_shake_fips_202_shake128_{}_json".format(
        msg_type.lower(),
    )
    for msg_type in [
        "ShortMsg",
        "LongMsg",
        "VariableOut",
    ]
] + [
    "//sw/host/cryptotest/testvectors/data:hjson_shake128",
]

SHAKE128_TESTVECTOR_ARGS = " ".join([
    "--hash-json=\"$(rootpath {})\"".format(target)
    for target in SHAKE128_TESTVECTOR_TARGETS
])

cryptotest(
    name = "shake128_kat",
    test_args = SHAKE128_TESTVECTOR_ARGS,
    test_harness = "//sw/host/tests/crypto/hash_kat:harness",
    test_vectors = SHAKE128_TESTVECTOR_TARGETS,
)

SHAKE256_TESTVECTOR_TARGETS = [
    "//sw/host/cryptotest/testvectors/data:nist_cavp_shake_fips_202_shake256_{}_json".format(
        msg_type.lower(),
    )
    for msg_type in [
        "ShortMsg",
        "LongMsg",
        "VariableOut",
    ]
] + [
    "//sw/host/cryptotest/testvectors/data:hjson_shake256",
]

SHAKE256_TESTVECTOR_ARGS = " ".join([
    "--hash-json=\"$(rootpath {})\"".format(target)
    for target in SHAKE256_TESTVECTOR_TARGETS
])

cryptotest(
    name = "shake256_kat",
    test_args = SHAKE256_TESTVECTOR_ARGS,
    test_harness = "//sw/host/tests/crypto/hash_kat:harness",
    test_vectors = SHAKE256_TESTVECTOR_TARGETS,
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

HMAC_SHA256_TESTVECTOR_TARGETS = [
    "//sw/host/cryptotest/testvectors/data:wycheproof_hmac_sha256.json",
    "//sw/host/cryptotest/testvectors/data:nist_cavp_hmac_sha256_fips_198_1_json",
]

HMAC_SHA256_TESTVECTOR_ARGS = " ".join([
    "--hmac-json=\"$(rootpath {})\"".format(target)
    for target in HMAC_SHA256_TESTVECTOR_TARGETS
])

cryptotest(
    name = "hmac_sha256_kat",
    test_args = HMAC_SHA256_TESTVECTOR_ARGS,
    test_harness = "//sw/host/tests/crypto/hmac_kat:harness",
    test_vectors = HMAC_SHA256_TESTVECTOR_TARGETS,
)

HMAC_SHA384_TESTVECTOR_TARGETS = [
    "//sw/host/cryptotest/testvectors/data:wycheproof_hmac_sha384.json",
    "//sw/host/cryptotest/testvectors/data:nist_cavp_hmac_sha384_fips_198_1_json",
]

HMAC_SHA384_TESTVECTOR_ARGS = " ".join([
    "--hmac-json=\"$(rootpath {})\"".format(target)
    for target in HMAC_SHA384_TESTVECTOR_TARGETS
])

cryptotest(
    name = "hmac_sha384_kat",
    test_args = HMAC_SHA384_TESTVECTOR_ARGS,
    test_harness = "//sw/host/tests/crypto/hmac_kat:harness",
    test_vectors = HMAC_SHA384_TESTVECTOR_TARGETS,
)

HMAC_SHA512_TESTVECTOR_TARGETS = [
    "//sw/host/cryptotest/testvectors/data:wycheproof_hmac_sha512.json",
    "//sw/host/cryptotest/testvectors/data:nist_cavp_hmac_sha512_fips_198_1_json",
]

HMAC_SHA512_TESTVECTOR_ARGS = " ".join([
    "--hmac-json=\"$(rootpath {})\"".format(target)
    for target in HMAC_SHA512_TESTVECTOR_TARGETS
])

cryptotest(
    name = "hmac_sha512_kat",
    test_args = HMAC_SHA512_TESTVECTOR_ARGS,
    test_harness = "//sw/host/tests/crypto/hmac_kat:harness",
    test_vectors = HMAC_SHA512_TESTVECTOR_TARGETS,
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

SPHINCSPLUS_TESTVECTOR_TARGETS = [
    "//sw/host/cryptotest/testvectors/data:{}".format(target)
    for target in [
        "rsp_sphincsplus_sha256_128s_simple_json",
    ]
]

SPHINCSPLUS_TESTVECTOR_ARGS = " ".join([
    "--sphincsplus-json=\"$(rootpath {})\"".format(target)
    for target in SPHINCSPLUS_TESTVECTOR_TARGETS
])

cryptotest(
    name = "sphincsplus_kat",
    test_args = SPHINCSPLUS_TESTVECTOR_ARGS,
    test_harness = "//sw/host/tests/crypto/sphincsplus_kat:harness",
    test_vectors = SPHINCSPLUS_TESTVECTOR_TARGETS,
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
        ":hmac_sha256_kat",
        ":hmac_sha384_kat",
        ":hmac_sha512_kat",
        ":kmac_kat",
        ":sha256_kat",
        ":sha384_kat",
        ":sha3_256_kat",
        ":sha3_384_kat",
        ":sha3_512_kat",
        ":sha512_kat",
        ":shake128_kat",
        ":shake256_kat",
        ":sphincsplus_kat",
    ],
)
