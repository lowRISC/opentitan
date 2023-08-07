# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_binary")

package(default_visibility = ["//visibility:public"])

# Since rust seems generally unfriendly to generated code, the PKCS#11 constants
# should be regenerated whenever we change the version of the rust-cryptoki library
# and then copied into //sw/host/hsmtool/src/util/attribute
filegroup(
    name = "generated_srcs",
    srcs = [
        ":attribute_type",
        ":certificate_type",
        ":key_type",
        ":mechanism_type",
        ":object_class",
    ],
    tags = ["manual"],
)

alias(
    name = "binding_srcs",
    actual = "@crate_index__cryptoki-sys-0.1.6//:binding_srcs",
)

py_binary(
    name = "pkcs11_consts",
    srcs = ["pkcs11_consts.py"],
)

genrule(
    name = "object_class",
    srcs = [":binding_srcs"],
    outs = ["object_class.rs"],
    cmd = """
        $(execpath :pkcs11_consts) \
            --binding $(rootpaths :binding_srcs) \
            --serde --conv_data CKO cryptoki::object::ObjectClass \
            | $(location @rules_rust//rust/toolchain:current_rustfmt_files) > $@
    """,
    tags = ["manual"],
    tools = [
        ":pkcs11_consts",
        "@rules_rust//rust/toolchain:current_rustfmt_files",
    ],
)

genrule(
    name = "key_type",
    srcs = [":binding_srcs"],
    outs = ["key_type.rs"],
    cmd = """
        $(execpath :pkcs11_consts) \
            --binding $(rootpaths :binding_srcs) \
            --serde --conv_data CKK cryptoki::object::KeyType \
            | $(location @rules_rust//rust/toolchain:current_rustfmt_files) > $@
    """,
    tags = ["manual"],
    tools = [
        ":pkcs11_consts",
        "@rules_rust//rust/toolchain:current_rustfmt_files",
    ],
)

genrule(
    name = "certificate_type",
    srcs = [":binding_srcs"],
    outs = ["certificate_type.rs"],
    cmd = """
        $(execpath :pkcs11_consts) \
            --binding $(rootpaths :binding_srcs) \
            --serde --conv_data CKC cryptoki::object::CertificateType \
            | $(location @rules_rust//rust/toolchain:current_rustfmt_files) > $@
    """,
    tags = ["manual"],
    tools = [
        ":pkcs11_consts",
        "@rules_rust//rust/toolchain:current_rustfmt_files",
    ],
)

genrule(
    name = "mechanism_type",
    srcs = [":binding_srcs"],
    outs = ["mechanism_type.rs"],
    cmd = """
        $(execpath :pkcs11_consts) \
            --binding $(rootpaths :binding_srcs) \
            --serde --conv_data CKM cryptoki::mechanism::MechanismType \
            | $(location @rules_rust//rust/toolchain:current_rustfmt_files) > $@
    """,
    tags = ["manual"],
    tools = [
        ":pkcs11_consts",
        "@rules_rust//rust/toolchain:current_rustfmt_files",
    ],
)

genrule(
    name = "attribute_type",
    srcs = [":binding_srcs"],
    outs = ["attribute_type.rs"],
    cmd = """
        $(execpath :pkcs11_consts) \
            --binding $(rootpaths :binding_srcs) \
            --serde --strum CKA cryptoki::object::AttributeType \
            | $(location @rules_rust//rust/toolchain:current_rustfmt_files) > $@
    """,
    tags = ["manual"],
    tools = [
        ":pkcs11_consts",
        "@rules_rust//rust/toolchain:current_rustfmt_files",
    ],
)
