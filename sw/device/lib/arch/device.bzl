# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Rules for capturing information necessary for executing on particular
devices and tops."""

load("//rules:rv.bzl", "OPENTITAN_PLATFORM", "rv_rule")

DeviceInfo = provider(
    doc = "Info needed to build and execute an OT binary.",
    fields = [
        "platform",
        "device_impl",
        "runner",
        "is_dv",
        "uses_vmem",
        "data",
        "otp",
        "dvsim_config",
        "default_args",
        "required_args",
    ],
)

def _opentitan_test_platform_impl(ctx):
    return [DeviceInfo(
        platform = ctx.attr.platform,
        device_impl = ctx.attr.device_impl,
        is_dv = ctx.attr.is_dv,
        uses_vmem = ctx.attr.uses_vmem,
        runner = ctx.attr.runner,
        data = ctx.attr.data,
        otp = ctx.attr.otp,
        default_args = ctx.attr.default_args,
        dvsim_config = ctx.file.dvsim_config,
        required_args = ctx.attr.required_args,
    )]

opentitan_device = rv_rule(
    implementation = _opentitan_test_platform_impl,
    doc = "Declares a device platform that an OpenTitan binary can be executed on.",
    attrs = {
        "platform": attr.string(default = OPENTITAN_PLATFORM),
        "device_impl": attr.label(
            doc = "The //sw/device/arch:device implementation for this device.",
            mandatory = True,
            providers = [CcInfo],
        ),
        "is_dv": attr.bool(
            doc = "Whether this is a DV target, requiring extra DV outputs.",
            default = False,
        ),
        "uses_vmem": attr.bool(
            doc = "Whether this target uses VMEM-formatted binaries.",
            default = False,
        ),
        "runner": attr.label(
            doc = "The executable used to actually drive tests on this device.",
            cfg = "host",
            mandatory = True,
            executable = True,
            allow_single_file = True,
        ),
        "data": attr.label_list(
            doc = "Data for the test runner.",
            cfg = "host",
            allow_files = True,
        ),
        "otp": attr.label(
            doc = "The default OTP image to use for testing.",
            default = Label("//hw/ip/otp_ctrl/data:rma_image_verilator"),
        ),
        "dvsim_config": attr.label(
            doc = "The default dvsim config to use for testing.",
            default = None,
            allow_single_file = True,
        ),
        "default_args": attr.string_list(
            doc = "Overrideable args for the test runner.",
            default = [],
        ),
        "required_args": attr.string_list(
            doc = "Non-overrideable args for the test runner.",
            default = [],
        ),
    },
    provides = [DeviceInfo],
)
