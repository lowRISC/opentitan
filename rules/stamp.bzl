# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Utilities to detect whether --stamp was specified on the command-line.
# This relies on the workaround explained in
# https://github.com/bazelbuild/bazel/issues/11164#issuecomment-617336309

# Return a rule attribute to add a stamp parameters. This stamping parameter follows
# the usual bazel convention:
# - `stamp = 1` means that stamping information is available, even if stamping is
#   disabled on the command line (`--nostamp`).
# - `stamp = 0` means that stamping information is not available, even if stamping is
#   is enabled on the command line (`--stamp`).
# - `stamp = -1` means that stamping is controlled by the command line `--stamp` or
#   `--nostamp` flags.
# See https://bazel.build/docs/user-manual#workspace-status for more information
# on stamping.
#
# The first argument of that macro is the default value of the `stamp` attribute.
# The second argument of that macro is the label of a stamp flag defined using `stamp_flag`.
#
# Use the `stamping_enabled` macro in the rule implementation to determine whether stamping
# is enabled.
def stamp_attr(default_value, stamp_flag):
    return {
        "stamp": attr.int(
            doc = """Whether to provide access to stamping information to the rule.""",
            default = default_value,
            values = [-1, 0, 1],
        ),
        "_stamp_flag": attr.label(
            default = stamp_flag,
            providers = [StampFlag],
        ),
    }

# See `stamp_flag`
StampFlag = provider("Value of --stamp", fields = ["stamp_flag"])

def _stamp_flag_impl(ctx):
    return [StampFlag(stamp_flag = ctx.attr.value)]

_stamp_flag = rule(
    implementation = _stamp_flag_impl,
    attrs = {
        "value": attr.bool(
            doc = "The value of the stamp flag",
            mandatory = True,
        ),
    },
    provides = [StampFlag],
)

# Define a stamping configuration flag to be used with `stamp_attr`.
# This is convoluted because we cannot use select in default attributes of rules.
# Hence we need define a rule just for the purpose of selecting its value using
# a configuration setting.
def stamp_flag(name):
    native.config_setting(
        name = name + "_config",
        values = {"stamp": "1"},
    )

    _stamp_flag(
        name = name,
        value = select({
            name + "_config": True,
            "//conditions:default": False,
        }),
    )

# Determine whether stamping is enabled, see `stamp_attr`.
# Pass the rule context as argument.
def stamping_enabled(ctx):
    stamp_attr = ctx.attr.stamp
    if stamp_attr == -1:
        return ctx.attr._stamp_flag[StampFlag].stamp_flag
    elif stamp_attr == 0:
        return False
    else:
        return True
