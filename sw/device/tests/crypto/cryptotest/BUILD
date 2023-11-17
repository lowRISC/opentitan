# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load(
    "//rules/opentitan:defs.bzl",
    "cw310_params",
    "hyper310_params",
    "opentitan_binary",
    "opentitan_test",
)

package(default_visibility = ["//visibility:public"])

# TODO(#20277): Running all test vectors causes the UART on the device to fail after about 140 seconds.
# For now, split the tests by the block mode to avoid the 140 second limit.
# testvector_targets = [
#     "//sw/host/cryptotest/testvectors/data/aes_nist_kat:{}_{}_{}_json".format(alg, kat_type, key_len)
#     for alg in ("cbc", "cfb128", "ecb", "ofb")
#     for kat_type in ("varkey", "gfsbox", "vartxt", "keysbox")
#     for key_len in ("128", "192", "256")
# ]

# testvector_args = " ".join([
#     "--aes-json=\"$(rootpath {})\"".format(target)
#     for target in testvector_targets
# ])

# opentitan_test(
#     name = "aes_kat_test",
#     cw310 = cw310_params(
#         timeout = "long",
#         binaries = {"//sw/device/tests/crypto/cryptotest/firmware:firmware": "firmware"},
#         data = testvector_targets,
#         test_cmd = """
#             --bootstrap={firmware}
#             --bitstream={bitstream}
#         """ + testvector_args,
#         test_harness = "//sw/host/tests/crypto/aes_nist_kat:harness",
#     ),
#     exec_env = {
#         "//hw/top_earlgrey:fpga_cw310_test_rom": None,
#         "//hw/top_earlgrey:fpga_hyper310_test_rom": None,
#     },
#     hyper310 = hyper310_params(
#         timeout = "long",
#         binaries = {"//sw/device/tests/crypto/cryptotest/firmware:firmware": "firmware"},
#         data = testvector_targets,
#         test_cmd = """
#             --bootstrap={firmware}
#             --bitstream={bitstream}
#         """ + testvector_args,
#         test_harness = "//sw/host/tests/crypto/aes_nist_kat:harness",
#     ),
# )

KAT_TYPE = [
    "varkey",
    "gfsbox",
    "vartxt",
    "keysbox",
]

KEY_LEN = [
    "128",
    "192",
    "256",
]

TESTVECTOR_TARGETS = {
    "cbc": [
        "//sw/host/cryptotest/testvectors/data/aes_nist_kat:cbc_{}_{}_json".format(kat_type, key_len)
        for kat_type in KAT_TYPE
        for key_len in KEY_LEN
    ],
    "cfb128": [
        "//sw/host/cryptotest/testvectors/data/aes_nist_kat:cfb128_{}_{}_json".format(kat_type, key_len)
        for kat_type in KAT_TYPE
        for key_len in KEY_LEN
    ],
    "ecb": [
        "//sw/host/cryptotest/testvectors/data/aes_nist_kat:ecb_{}_{}_json".format(kat_type, key_len)
        for kat_type in KAT_TYPE
        for key_len in KEY_LEN
    ],
    "ofb": [
        "//sw/host/cryptotest/testvectors/data/aes_nist_kat:ofb_{}_{}_json".format(kat_type, key_len)
        for kat_type in KAT_TYPE
        for key_len in KEY_LEN
    ],
}

TESTVECTOR_ARGS = {
    "cbc": " ".join([
        "--aes-json=\"$(rootpath {})\"".format(target)
        for target in TESTVECTOR_TARGETS["cbc"]
    ]),
    "cfb128": " ".join([
        "--aes-json=\"$(rootpath {})\"".format(target)
        for target in TESTVECTOR_TARGETS["cfb128"]
    ]),
    "ecb": " ".join([
        "--aes-json=\"$(rootpath {})\"".format(target)
        for target in TESTVECTOR_TARGETS["ecb"]
    ]),
    "ofb": " ".join([
        "--aes-json=\"$(rootpath {})\"".format(target)
        for target in TESTVECTOR_TARGETS["ofb"]
    ]),
}

[
    opentitan_test(
        name = "aes_{}_kat".format(mode),
        cw310 = cw310_params(
            timeout = "long",
            binaries = {"//sw/device/tests/crypto/cryptotest/firmware:firmware": "firmware"},
            data = TESTVECTOR_TARGETS[mode],
            test_cmd = """
                --bootstrap={firmware}
                --bitstream={bitstream}
            """ + TESTVECTOR_ARGS[mode],
            test_harness = "//sw/host/tests/crypto/aes_nist_kat:harness",
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        },
        hyper310 = hyper310_params(
            timeout = "long",
            binaries = {"//sw/device/tests/crypto/cryptotest/firmware:firmware": "firmware"},
            data = TESTVECTOR_TARGETS[mode],
            test_cmd = """
                --bootstrap={firmware}
                --bitstream={bitstream}
            """ + TESTVECTOR_ARGS[mode],
            test_harness = "//sw/host/tests/crypto/aes_nist_kat:harness",
        ),
    )
    for mode in [
        "cbc",
        "cfb128",
        "ecb",
        "ofb",
    ]
]
