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
            --bitstream={bitstream}
        """ + testvector_args,
        test_harness = "//sw/host/tests/crypto/aes_nist_kat:harness",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
    },
)
