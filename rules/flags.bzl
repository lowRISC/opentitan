# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_pkg//pkg:providers.bzl", "PackageDirsInfo", "PackageFilegroupInfo", "PackageFilesInfo", "PackageSymlinkInfo")

_KNOWN_PROVIDERS = [
    PackageDirsInfo,
    PackageFilegroupInfo,
    PackageFilesInfo,
    PackageSymlinkInfo,
    OutputGroupInfo,
]

def _bool(v):
    if v in ("True", "true"):
        return True
    if v in ("False", "false"):
        return False
    fail("Boolean value must be 'True' or 'False'")

_FLAG_CONVERSIONS = {
    # TODO: this needs to be the superset of all flags you might want to
    # modify during the build and an appropriate type conversion function.
    "//sw/host/opentitantool:static_link": _bool,
}

def _flags_transition_impl(settings, attr):
    result = {}
    for label, value in attr.flags.items():
        label = str(label)
        if label.startswith("@@//"):
            label = label[2:]
        result[label] = _FLAG_CONVERSIONS[label](value)
    return result

flags_transition = transition(
    implementation = _flags_transition_impl,
    inputs = [],
    outputs = _FLAG_CONVERSIONS.keys(),
)

def _build_with_flags_impl(ctx):
    # Start with DefaultInfo and then forward on any other providers we know about.
    result = [ctx.attr.target[DefaultInfo]]
    for p in _KNOWN_PROVIDERS:
        if p in ctx.attr.target:
            result.append(ctx.attr.target[p])
    return result

build_with_flags = rule(
    implementation = _build_with_flags_impl,
    cfg = flags_transition,
    attrs = {
        "target": attr.label(doc = "Target to build with flags"),
        "flags": attr.label_keyed_string_dict(doc = "Mapping of flag labels to values"),
        "_allowlist_function_transition": attr.label(default = "@bazel_tools//tools/allowlists/function_transition_allowlist"),
    },
)
