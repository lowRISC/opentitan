# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

MODE = [
    "CBC",
    "CFB128",
    "ECB",
    "OFB",
]

TEST = [
    "GFSbox",
    "KeySbox",
    "VarKey",
    "VarTxt",
]

SIZE = [
    "128",
    "192",
    "256",
]

# Raw testvector sources are named as "{mode}{test}{size}.rsp".
# E.g. CBCGFSbox128.rsp
# Cryptotest uses the form {mode}_{test}_{size}".
# E.g. cbc_gfsbox_128
testcases = [
    {
        "nist_name": "{}{}{}".format(mode, test, size),
        "cryptotest_name": "{}_{}_{}".format(
            mode.lower(),
            test.lower(),
            size.lower(),
        ),
        "mode": mode.lower(),
        "test_type": test.lower(),
        "size": size,
    }
    for mode in MODE
    for test in TEST
    for size in SIZE
]

[
    filegroup(
        name = "{}_raw".format(test["cryptotest_name"]),
        srcs = ["{}.rsp".format(test["nist_name"])],
    )
    for test in testcases
]

[
    genrule(
        name = "{}_json".format(test["cryptotest_name"]),
        srcs = [
            ":{}_raw".format(test["cryptotest_name"]),
            "//sw/host/cryptotest/testvectors/data/schemas:aes_block_schema",
        ],
        outs = ["{}.json".format(test["cryptotest_name"])],
        cmd = """$(location //sw/host/cryptotest/testvectors/parsers:nist_aes_parser) \
                $(location :{}_raw) \
                $(RULEDIR)/{} {} {} \
                $(location //sw/host/cryptotest/testvectors/data/schemas:aes_block_schema)""".format(
            test["cryptotest_name"],
            test["cryptotest_name"],
            test["mode"],
            test["size"],
        ),
        message = "Parsing testvector - NIST AES KAT - {}".format(test["cryptotest_name"]),
        tools = ["//sw/host/cryptotest/testvectors/parsers:nist_aes_parser"],
        visibility = ["//visibility:public"],
    )
    for test in testcases
]
