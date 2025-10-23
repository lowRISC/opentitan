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
    #
    # The transition _also_ has to emit a value for every item specified in
    # the transition outputs.  We may want to also encode default values
    # here when this list grows so that users of the `build_with_flags`
    # rule don't have to supply all the flags.
    str(Label("@lowrisc_opentitan//rules:static_link_host_tools")): _bool,
}

def _flags_transition_impl(settings, attr):
    result = {}
    for label, value in attr.flags.items():
        label = str(Label(label))
        if label not in _FLAG_CONVERSIONS:
            fail(label, "is not an allowed flag")
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
