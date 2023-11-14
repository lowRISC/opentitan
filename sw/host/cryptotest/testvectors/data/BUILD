# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

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
    visibility = ["//visibility:public"],
)
