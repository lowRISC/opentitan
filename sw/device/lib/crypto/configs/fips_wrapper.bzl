# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:defs.bzl", "opentitan_test")

def _fips_transition_impl(settings, attr):
    return {
        "//sw/device/lib/crypto/configs:cryptolib_config_flag": "crypto_fips_all",
        "//sw/device/lib/crypto/configs:hashed_flag": True,
        "//sw/device/lib/crypto/configs:type_flag": "binary_blob",
    }

fips_transition = transition(
    implementation = _fips_transition_impl,
    inputs = [],
    outputs = [
        "//sw/device/lib/crypto/configs:cryptolib_config_flag",
        "//sw/device/lib/crypto/configs:hashed_flag",
        "//sw/device/lib/crypto/configs:type_flag",
    ],
)

def _fips_test_wrapper_impl(ctx):
    actual_test = ctx.executable.actual_test

    executable = ctx.actions.declare_file(ctx.label.name)

    # Create a symlink to the transitioned test executable
    ctx.actions.symlink(
        output = executable,
        target_file = actual_test,
        is_executable = True,
    )

    # Gather runfiles
    runfiles = ctx.runfiles(files = [actual_test])
    runfiles = runfiles.merge(ctx.attr.actual_test[0].default_runfiles)

    # Bundle the transitioned data files into the execution environment
    if hasattr(ctx.attr, "data"):
        for d in ctx.attr.data:
            runfiles = runfiles.merge(d[DefaultInfo].default_runfiles)
            runfiles = runfiles.merge(ctx.runfiles(files = d.files.to_list()))

    return [DefaultInfo(
        executable = executable,
        runfiles = runfiles,
    )]

# Create a wrapper for a test to run with the --config=crypto_fips_all flag
fips_transition_test = rule(
    implementation = _fips_test_wrapper_impl,
    test = True,
    attrs = {
        "actual_test": attr.label(executable = True, cfg = fips_transition),
        "data": attr.label_list(allow_files = True, cfg = fips_transition),
        "_allowlist_function_transition": attr.label(
            default = "@bazel_tools//tools/allowlists/function_transition_allowlist",
        ),
    },
)

# Generates a wrapper for an opentitan_test to run with the --config=crypto_fips_all flag
def fips_wrap_opentitan_test(name, exec_env):
    for env_label in exec_env.keys():
        env_suffix = env_label.split(":")[-1]

        # The new name of the test is {name}_fips_{exec_env}
        fips_transition_test(
            name = "{}_fips_{}".format(name, env_suffix),
            actual_test = ":{}_{}".format(name, env_suffix),
        )
