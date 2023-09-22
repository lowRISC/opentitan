# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Helper rules for generating artefacts used by QEMU.

The QEMU OT port uses a custom data format for both the flash and the OTP
images. This file provide rules to produce those from the "standard" format
used by the rest of the build system.
"""

load("@lowrisc_opentitan//rules:rv.bzl", "rv_rule")

def _qemu_flashgen_impl(ctx):
    raw_flash = ctx.actions.declare_file(ctx.attr.output)
    outputs = [raw_flash]
    outputs.append(raw_flash)
    inputs = []

    # These flags tell flashgen  (an OpenTitan-specific script) to create an image from scratch
    # and not to check that input files are valid before processing them for QEMU. This is
    # necessary because some of the tests involved using invalid files on purpose.
    arguments = ["-D", "-A"]
    for binary, offset in ctx.attr.binaries.items():
        inputs.extend(binary.files.to_list())
        arguments.append("--otdesc")
        arguments.append("{}@{}".format(binary.files.to_list()[0].path, offset))
    arguments.append(raw_flash.path)

    # TODO add ELF file support
    ctx.actions.run(
        outputs = outputs,
        inputs = inputs,
        arguments = arguments,
        executable = ctx.executable._flashgen,
    )
    return [DefaultInfo(
        files = depset(outputs),
        data_runfiles = ctx.runfiles(files = outputs),
    )]

# TODO add ELF file support
qemu_flashgen = rv_rule(
    implementation = _qemu_flashgen_impl,
    doc = """
Generate a QEMU flash image from a one or more binaries.
This rule calls the flashgen.py script from QEMU OT port under the hood.

Since the flash only contains the binary, all debug information is lost.
To remedy this, the QEMU OT port supports adding information about the ELF
files in the flashthat can then be loaded by the emulator when disassembling
code using the console.
""",
    attrs = {
        "output": attr.string(doc = "Output file containing the QEMU flash image"),
        "binaries": attr.label_keyed_string_dict(
            allow_empty = False,
            doc = """
A dictionary where keys are the binaries and values are the offsets where to put
them in the flash. This is the same format accepted by the assemble_flash_image rule.
""",
        ),
        "_flashgen": attr.label(
            default = "@//third_party/qemu_ot:flashgen",
            executable = True,
            cfg = "exec",
        ),
    },
)

def _qemu_otpconv_impl(ctx):
    outputs = []
    raw_otp = ctx.actions.declare_file("{}.raw".format(ctx.label.name))
    outputs.append(raw_otp)
    ctx.actions.run(
        outputs = [raw_otp],
        inputs = [
            ctx.file.img,
        ],
        arguments = [
            "--input",
            ctx.file.img.path,
            "--output",
            raw_otp.path,
        ],
        executable = ctx.executable._otpconv,
    )
    return [DefaultInfo(
        files = depset(outputs),
        data_runfiles = ctx.runfiles(files = outputs),
    )]

qemu_otpconv = rv_rule(
    implementation = _qemu_otpconv_impl,
    doc = """
Generate a QEMU OTP image from a "standard" OTP image.
This rule calls the otpconv.py script from QEMU OT port under the hood.
""",
    attrs = {
        "img": attr.label(
            allow_single_file = True,
            doc = "The OTP image (produced by otp_image) to use.",
        ),
        "_otpconv": attr.label(
            default = "@//third_party/qemu_ot:otpconv",
            executable = True,
            cfg = "exec",
        ),
    },
)
