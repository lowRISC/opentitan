# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Rules for generating entropy buffer files.

Entropy buffer files are consumed by the OTP image generation tooling.
Specifically, they are used to generate the LC state encodings and OTP memory
map.
"""

load("@bazel_skylib//rules:common_settings.bzl", "BuildSettingInfo")

def _entropy_buffer_impl(ctx):
    output = ctx.actions.declare_file(ctx.attr.name + ".txt")
    args = ctx.actions.args()
    args.add("-n", ctx.attr.num_bytes)
    args.add("--seed", ctx.attr.seed[BuildSettingInfo].value)
    args.add("-o", output.path)
    ctx.actions.run(
        outputs = [output],
        arguments = [args],
        executable = ctx.executable._tool,
    )
    return [DefaultInfo(files = depset([output]), runfiles = ctx.runfiles(files = [output]))]

entropy_buffer = rule(
    implementation = _entropy_buffer_impl,
    attrs = {
        "num_bytes": attr.int(
            default = 20000,
            doc = "Number of bytes to generate.",
        ),
        "seed": attr.label(
            default = "//hw/ip/otp_ctrl/data:lc_seed",
            doc = "Custom seed for RNG to generate the entropy buffer.",
        ),
        "_tool": attr.label(
            default = "//util/topgen:entropy_buffer_generator",
            executable = True,
            cfg = "exec",
        ),
    },
)
