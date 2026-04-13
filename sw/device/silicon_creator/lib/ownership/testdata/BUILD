# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

exports_files([
    "basic_owner.json5",
    "basic_owner_testdata.h",
    "hybrid_owner.json5",
])

genrule(
    name = "hybrid_owner_bin",
    srcs = [
        "hybrid_owner.json5",
        "//sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key_pub",
        "//sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key_spx_pub",
    ],
    outs = ["hybrid_owner.bin"],
    cmd = """
        $(execpath //sw/host/opentitantool) --rcfile= \\
            ownership config --input $(location hybrid_owner.json5) $@
    """,
    tools = ["//sw/host/opentitantool"],
)

genrule(
    name = "hybrid_owner_digest",
    srcs = [":hybrid_owner_bin"],
    outs = ["hybrid_owner.digest"],
    cmd = """
        $(execpath //sw/host/opentitantool) --rcfile= \\
            ownership digest $(location :hybrid_owner_bin) --bin $@
    """,
    tools = ["//sw/host/opentitantool"],
)

genrule(
    name = "hybrid_owner_ecdsa_signature",
    srcs = [
        ":hybrid_owner_digest",
        "//sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key",
    ],
    outs = ["hybrid_owner.ecdsa_signature"],
    cmd = """
        $(execpath //sw/host/opentitantool) --rcfile= \\
            ecdsa sign  $(location //sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key) \\
            --input $(location :hybrid_owner_digest) --output $@
    """,
    tools = ["//sw/host/opentitantool"],
)

genrule(
    name = "hybrid_owner_spx_signature",
    srcs = [
        ":hybrid_owner_digest",
        "//sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key_spx",
    ],
    outs = ["hybrid_owner.spx_signature"],
    cmd = """
        $(execpath //sw/host/opentitantool) --rcfile= \\
            spx sign $(location :hybrid_owner_digest) \\
            $(location //sw/device/silicon_creator/lib/ownership/keys/dummy:owner_key_spx) \\
            --output $@ --domain PrehashedSha256
    """,
    tools = ["//sw/host/opentitantool"],
)
