# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load(
    "//rules/opentitan:defs.bzl",
    "cw310_params",
    "opentitan_binary",
    "opentitan_test",
)

package(default_visibility = ["//visibility:public"])

testvector_targets = [
    "//sw/host/cryptotest/testvectors/data/aes_nist_kat:{}_{}_{}_json".format(alg, kat_type, key_len)
    for alg in ("cbc", "cfb128", "ecb", "ofb")
    for kat_type in ("varkey", "gfsbox", "vartxt", "keysbox")
    for key_len in ("128", "192", "256")
]

testvector_args = " ".join([
    "--aes-json=\"$(rootpath {})\"".format(target)
    for target in testvector_targets
])

opentitan_test(
    name = "aes_kat_test",
    cw310 = cw310_params(
        timeout = "long",
        binaries = {"//sw/device/tests/crypto/cryptotest/firmware:firmware": "firmware"},
        data = testvector_targets,
        test_cmd = """
            --bootstrap={firmware}
        """ + testvector_args,
        test_harness = "//sw/host/tests/crypto/aes_nist_kat:harness",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
    },
)

ECDSA_TESTVECTOR_TARGETS = [
    "//sw/host/cryptotest/testvectors/data:wycheproof_ecdsa_{}.json".format(config)
    for config in [
        "p256_sha256",
        "p256_sha512",
        "p256_sha3_256",
        "p256_sha3_512",
        # TODO uncomment when cryptolib supports ECDSA with P-384
        #        "p384_sha384",
        #        "p384_sha512",
        #        "p384_sha3_384",
        #        "p384_sha3_512",
    ]
] + [
    "//sw/host/cryptotest/testvectors/data:nist_cavp_ecdsa_fips_186_4_sig_ver_json",
]

ECDSA_TESTVECTOR_ARGS = " ".join([
    "--ecdsa-json=\"$(rootpath {})\"".format(target)
    for target in ECDSA_TESTVECTOR_TARGETS
])

opentitan_test(
    name = "ecdsa_kat",
    cw310 = cw310_params(
        timeout = "long",
        binaries = {"//sw/device/tests/crypto/cryptotest/firmware:firmware": "firmware"},
        data = ECDSA_TESTVECTOR_TARGETS,
        test_cmd = """
            --bootstrap={firmware}
        """ + ECDSA_TESTVECTOR_ARGS,
        test_harness = "//sw/host/tests/crypto/ecdsa_kat:harness",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
    },
)

HASH_TESTVECTOR_TARGETS = [
    "//sw/host/cryptotest/testvectors/data:nist_cavp_{}_{}_{}_json".format(
        src_repo,
        algorithm.lower(),
        msg_type.lower(),
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
        #        "LongMsg",
    ] + extra_msg_types
]

HASH_TESTVECTOR_ARGS = " ".join([
    "--hash-json=\"$(rootpath {})\"".format(target)
    for target in HASH_TESTVECTOR_TARGETS
])

opentitan_test(
    name = "hash_kat",
    cw310 = cw310_params(
        timeout = "long",
        binaries = {"//sw/device/tests/crypto/cryptotest/firmware:firmware": "firmware"},
        data = HASH_TESTVECTOR_TARGETS,
        test_cmd = """
                --bootstrap={firmware}
            """ + HASH_TESTVECTOR_ARGS,
        test_harness = "//sw/host/tests/crypto/hash_kat:harness",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
    },
)
