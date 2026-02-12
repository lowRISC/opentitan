# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:util.bzl", "flatten")
load("@bazel_skylib//rules:common_settings.bzl", "string_flag")
load(
    "//rules:autogen.bzl",
    "opentitan_ip_c_header",
    "opentitan_ip_rust_module",
)
load("//rules/opentitan:hw.bzl", "get_top_attr")
load(
    "//hw/top:defs.bzl",
    "ALL_IP_NAMES",
    "ALL_SEED_NAMES",
    "ALL_TOPS",
    "ALL_TOP_NAMES",
    "opentitan_alias_top_attr",
    "opentitan_if_ip",
)
load("@rules_rust//rust:defs.bzl", "rust_library")

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "doc_files",
    srcs = glob(["**/*.md"]),
)

# Use this flag to select the top.
string_flag(
    name = "top",
    build_setting_default = "earlgrey",
    values = ALL_TOP_NAMES,
)

# Use this flag to select the seed.
string_flag(
    name = "seed",
    build_setting_default = "testing",
    values = ALL_SEED_NAMES,
)

# Config settings to test against tops.
[
    config_setting(
        name = "is_{}".format(top),
        flag_values = {
            ":top": top,
        },
    )
    for top in ALL_TOP_NAMES
]

# Config settings to test against seeds.
[
    config_setting(
        name = "is_seed_{}".format(seed),
        flag_values = {
            ":seed": seed,
        },
    )
    for seed in ALL_SEED_NAMES
]

opentitan_alias_top_attr(
    name = "top_gen_hjson",
    attr_name = "hjson",
)

# Point to the right top library.
opentitan_alias_top_attr(
    name = "top_lib",
    attr_name = "top_lib",
)

# Point to the right top library.
opentitan_alias_top_attr(
    name = "top_ld",
    attr_name = "top_ld",
)

opentitan_alias_top_attr(
    name = "top_otp_map",
    attr_name = "otp_map",
)

opentitan_alias_top_attr(
    name = "rtl_files",
    attr_name = "top_rtl",
)

# For each top, create a selecting alias for the seed.
[
    alias(
        name = "top_{}_seed_secrets".format(top.name),
        actual = select({
            ":is_seed_{}".format(seed): secrets
            for (seed, secrets) in get_top_attr(top, "secret_cfgs", False, {}).items()
        }),
        target_compatible_with = select({
            ":is_seed_{}".format(seed): []
            for seed in get_top_attr(top, "secret_cfgs", False, {}).keys()
        } | {
            "//conditions:default": ["@platforms//:incompatible"],
        }),
    )
    for top in ALL_TOPS
]

# Then create an alias overall
alias(
    name = "secrets",
    actual = select({
        "@lowrisc_opentitan//hw/top:is_{}".format(top): ":top_{}_seed_secrets".format(top)
        for top in ALL_TOP_NAMES
    }),
)

# C register headers for all IPs.
[
    opentitan_ip_c_header(
        name = "{}_c_regs".format(ip),
        ip = ip,
    )
    for ip in ALL_IP_NAMES
]

# Rust register modules for all IPs.
[
    opentitan_ip_rust_module(
        name = "{}_rust_regs".format(ip),
        ip = ip,
        kind = "generic",
    )
    for ip in ALL_IP_NAMES
]

# `lib.rs` file defining a module for each IP.
genrule(
    name = "ot_regs_lib_rs",
    srcs = [],
    outs = ["lib.rs"],
    cmd = "echo '{}' > \"$@\"".format(
        "\n".join([
            '#[cfg(feature = "{ip}")]\npub mod {ip};'.format(ip = ip)
            for ip in ALL_IP_NAMES
        ]),
    ),
    visibility = ["//visibility:private"],
)

# Crate with a module for the registers of each IP.
rust_library(
    name = "ot_regs",
    srcs = [":ot_regs_lib_rs"] + flatten([
        opentitan_if_ip(
            ip,
            [":{}_rust_regs".format(ip)],
            [],
        )
        for ip in ALL_IP_NAMES
    ]),
    crate_features = flatten([
        opentitan_if_ip(
            ip,
            [ip],
            [],
        )
        for ip in ALL_IP_NAMES
    ]),
)

cc_library(
    name = "doxy_target",
    deps = [
        # Pull all DT headers and implementation, transitively includes top headers.
        "//hw/top/dt",
    ] + flatten([
        # Add all compatible register headers
        opentitan_if_ip(
            ip,
            ["{}_c_regs".format(ip)],
            [],
        )
        for ip in ALL_IP_NAMES
    ]),
)
