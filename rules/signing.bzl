# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "@opentitan_signing_infra//signing:defs.bzl",
    _wrapped_offline_presigning_artifacts = "offline_presigning_artifacts",
)
load("//rules/opentitan:providers.bzl", "get_binary_files")
load("//rules/opentitan:toolchain.bzl", "LOCALTOOLS_TOOLCHAIN")

def _filter_binary_srcs_impl(ctx):
    """Filter a set of given sources to only their binary files.

    The separate OpenTitan signing rules do not know about the OpenTitan providers,
    and thus cannot filter for binaries themselves. Perform pre-filtering in a
    separate rule to allow wrapping and supporting external signing rules.
    """
    binary_srcs = get_binary_files(ctx.attr.srcs)
    return [
        DefaultInfo(files = depset(binary_srcs)),
    ]

_filter_binary_srcs = rule(
    implementation = _filter_binary_srcs_impl,
    attrs = {
        "srcs": attr.label_list(allow_files = True),
    },
    doc = "A rule to filter out binary sources from OpenTitan providers to provide to the external `offline_presigning_artifacts` rule.",
)

def offline_presigning_artifacts(name, srcs = [], **kwargs):
    filtered_target = "_{}_filtered_binary_srcs_internal".format(name)
    _filter_binary_srcs(
        name = filtered_target,
        srcs = srcs,
        testonly = kwargs.get("testonly", False),
        visibility = ["//visibility:private"],
    )

    return _wrapped_offline_presigning_artifacts(
        name = name,
        srcs = [":{}".format(filtered_target)],
        **kwargs
    )
