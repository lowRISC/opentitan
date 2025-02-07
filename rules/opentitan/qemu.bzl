# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "@lowrisc_opentitan//rules/opentitan:providers.bzl",
    "SimQemuBinaryInfo",
)
load(
    "@lowrisc_opentitan//rules/opentitan:util.bzl",
    "get_fallback",
    "get_override",
)
load(
    "//rules/opentitan:exec_env.bzl",
    "ExecEnvInfo",
    "common_test_setup",
    "exec_env_as_dict",
    "exec_env_common_attrs",
)
load("//rules/opentitan:toolchain.bzl", "LOCALTOOLS_TOOLCHAIN")

_TEST_SCRIPT = """#!/bin/bash
set -e

# QEMU requires mutable flash and OTP files but Bazel only provides RO
# files so we have to create copies unique to this test run.
cp {otp} {mutable_otp} && chmod +w {mutable_otp}
if [ ! -z {flash} ]; then
    cp {flash} {mutable_flash} && chmod +w {mutable_flash}
fi

echo Invoking test: {test_harness} {args} "$@"
{test_harness} {args} "$@"
"""

def qemu_params(
        tags = [],
        timeout = "short",
        local = True,
        test_harness = "//rules/scripts:qemu_pass",
        binaries = {},
        rom = None,
        rom_ext = None,
        otp = None,
        bitstream = None,
        test_cmd = "",
        data = [],
        defines = [],
        icount = 6,
        globals = {},
        **kwargs):
    extra_params = {
        "icount": str(icount),
        # We have to stringify this dictionary here because `_opentitan_test` only accepts
        # a dict with string values, not more dicts.
        "globals": json.encode(globals),
    }

    return struct(
        tags = tags,
        timeout = timeout,
        local = local,
        test_harness = test_harness,
        binaries = binaries,
        rom = rom,
        rom_ext = rom_ext,
        otp = otp,
        bitstream = bitstream,
        test_cmd = test_cmd,
        data = data,
        param = kwargs | extra_params,
        defines = defines,
    )

def gen_cfg(ctx, **kwargs):
    """Generate a QEMU `readconfig` INI file containing OpenTitan RTL secrets"""
    name = get_override(ctx, "label.name", kwargs)
    cfggen = get_override(ctx, "executable.cfggen", kwargs)

    otp_sv = get_override(ctx, "file.otp_sv", kwargs)
    lc_sv = get_override(ctx, "file.lc_sv", kwargs)
    top_hjson = get_override(ctx, "file.top_hjson", kwargs)

    top_name = get_override(ctx, "attr.top_name", kwargs)

    out = ctx.actions.declare_file(name + ".ini")

    ctx.actions.run(
        inputs = [otp_sv, lc_sv, top_hjson],
        outputs = [out],
        executable = cfggen[DefaultInfo].files_to_run,
        arguments = [
            "--out",
            out.path,
            "--top",
            top_name,
            "--topcfg",
            top_hjson.path,
            "--otpconst",
            otp_sv.path,
            "--lifecycle",
            lc_sv.path,
            ".",
        ],
        mnemonic = "CfgGen",
    )
    return out

qemu_cfg = rule(
    implementation = lambda ctx: [DefaultInfo(files = depset([gen_cfg(ctx)]))],
    attrs = {
        "top_name": attr.string(),
        "top_hjson": attr.label(allow_single_file = True),
        "otp_sv": attr.label(allow_single_file = True),
        "lc_sv": attr.label(allow_single_file = True),
        "cfggen": attr.label(
            executable = True,
            cfg = "exec",
            allow_files = True,
            default = Label("//third_party/qemu:cfggen"),
        ),
    },
)

def gen_otp(ctx, **kwargs):
    """Generate a QEMU-compatible OTP image"""
    name = get_override(ctx, "label.name", kwargs)
    out = ctx.actions.declare_file(name + ".raw")

    vmem = get_override(ctx, "file.vmem", kwargs)
    otptool = get_override(ctx, "executable.otptool", kwargs)

    ctx.actions.run(
        inputs = [vmem],
        outputs = [out],
        executable = otptool[DefaultInfo].files_to_run,
        arguments = [
            "-m",
            vmem.path,
            "-r",
            out.path,
            "-k",
            "otp",
        ],
        mnemonic = "OtpGen",
    )
    return out

qemu_otp = rule(
    implementation = lambda ctx: [DefaultInfo(files = depset([gen_otp(ctx)]))],
    attrs = {
        "vmem": attr.label(allow_single_file = True),
        "otptool": attr.label(
            executable = True,
            cfg = "exec",
            allow_files = True,
            default = Label("//third_party/qemu:otptool"),
        ),
    },
)

# NOTE: currently only single-bank flash programs are supported.
def gen_flash(ctx, **kwargs):
    """\
    Generate a QEMU-compatible flash image.

    NOTE: currently only single-bank flash images are supported.
    """
    name = get_override(ctx, "label.name", kwargs)
    out = ctx.actions.declare_file(name + ".qemu_bin")

    firmware_bin = get_override(ctx, "file.firmware_bin", kwargs)
    firmware_elf = get_override(ctx, "file.firmware_elf", kwargs)

    flashgen = get_override(ctx, "executable.flashgen", kwargs)

    ctx.actions.run(
        inputs = [firmware_bin, firmware_elf],
        outputs = [out],
        executable = flashgen[DefaultInfo].files_to_run,
        arguments = [
            "-x",
            firmware_bin.path,
            "-X",
            firmware_elf.path,
            # Skip `flashgen`'s ELF/binary mtime checks - it will fail if the
            # binary is older than the ELF which usually suggests that the
            # binary has not been regenerated, however Bazel often messes with
            # mtimes causing false negatives.
            "--ignore-time",
            out.path,
        ],
        mnemonic = "FlashGen",
    )
    return out

qemu_flash = rule(
    implementation = lambda ctx: [DefaultInfo(files = depset([gen_flash(ctx)]))],
    attrs = {
        "firmware_bin": attr.label(
            allow_single_file = True,
            doc = "Binary firmware to be run after the ROM, usually signed",
        ),
        "firmware_elf": attr.label(
            allow_single_file = True,
            doc = "ELF version of the `firmware_bin` attribute for symbol tracking",
        ),
        "flashgen": attr.label(
            executable = True,
            cfg = "exec",
            allow_files = True,
            default = Label("//third_party/qemu:flashgen"),
        ),
    },
)

def _sim_qemu(ctx):
    fields = exec_env_as_dict(ctx)
    return ExecEnvInfo(
        provider = SimQemuBinaryInfo,
        test_dispatch = _test_dispatch,
        transform = _transform,
        cfggen = ctx.attr.cfggen,
        otptool = ctx.attr.otptool,
        flashgen = ctx.attr.flashgen,
        otp_sv = ctx.file.otp_sv,
        lc_sv = ctx.file.lc_sv,
        top_hjson = ctx.file.top_hjson,
        **fields
    )

sim_qemu = rule(
    implementation = _sim_qemu,
    attrs = exec_env_common_attrs() | {
        "cfggen": attr.label(
            executable = True,
            cfg = "exec",
            allow_files = True,
            default = Label("//third_party/qemu:cfggen"),
        ),
        "otptool": attr.label(
            executable = True,
            cfg = "exec",
            allow_files = True,
            default = Label("//third_party/qemu:otptool"),
        ),
        "flashgen": attr.label(
            executable = True,
            cfg = "exec",
            allow_files = True,
            default = Label("//third_party/qemu:flashgen"),
        ),
        "otp_sv": attr.label(
            allow_single_file = True,
            # TODO: should we really use Earl Grey as the default?
            default = Label("//hw/top_earlgrey/ip_autogen/otp_ctrl:rtl/otp_ctrl_part_pkg.sv"),
        ),
        "lc_sv": attr.label(
            allow_single_file = True,
            default = Label("//hw/ip/lc_ctrl:rtl/lc_ctrl_state_pkg.sv"),
        ),
        "top_hjson": attr.label(
            allow_single_file = True,
            default = Label("//hw/top_earlgrey/data/autogen:top_earlgrey.gen.hjson"),
        ),
    },
    toolchains = [LOCALTOOLS_TOOLCHAIN],
)

def _transform(ctx, exec_env, name, elf, binary, signed_bin, disassembly, mapfile):
    if ctx.attr.kind == "rom":
        default = elf
        rom = elf
    elif ctx.attr.kind == "ram":
        default = elf
        rom = None
    elif ctx.attr.kind == "flash":
        default = gen_flash(
            ctx,
            flashgen = exec_env.flashgen,
            firmware_bin = signed_bin or binary,
            firmware_elf = elf,
        )
        rom = exec_env.rom[SimQemuBinaryInfo].rom
    else:
        fail("Not implemented: kind == ", ctx.attr.kind)

    otp = gen_otp(
        ctx,
        otptool = exec_env.otptool,
        vmem = exec_env.otp,
    )

    qemu_cfg = gen_cfg(
        ctx,
        cfggen = exec_env.cfggen,
        otp_sv = exec_env.otp_sv,
        lc_sv = exec_env.lc_sv,
        top_hjson = exec_env.top_hjson,
        top_name = exec_env.design,
    )

    return {
        "elf": elf,
        "binary": binary,
        "default": default,
        "rom": rom,
        "rom32": None,
        "signed_bin": signed_bin,
        "disassembly": disassembly,
        "mapfile": mapfile,
        "hashfile": None,
        "qemu_cfg": qemu_cfg,
        "otp": otp,
    }

def _test_dispatch(ctx, exec_env, firmware):
    """Dispatch a test for the sim_qemu environment.

    Args:
      ctx: The rule context.
      exec_env: The ExecEnvInfo for this environment.
      firmware: A label with a SimQemuBinaryInfo provider attached.
    Returns:
      (File, List[File]) The test script and needed runfiles.
    """

    test_harness, data_labels, data_files, param, action_param = common_test_setup(ctx, exec_env, firmware)

    data_files += [firmware.qemu_cfg, firmware.otp]
    test_script_fmt = {}

    # Get the pre-test_cmd args.
    args = get_fallback(ctx, "attr.args", exec_env)
    args = " ".join(args).format(**param)
    args = ctx.expand_location(args, data_labels)

    # Add arguments to pass directly to QEMU.
    qemu_args = []

    qemu_args += ["-display", "none"]
    qemu_args += ["-M", "ot-{}".format(exec_env.design)]

    # Provide top-specific files.
    qemu_args += ["-readconfig", "{}".format(firmware.qemu_cfg.short_path)]
    qemu_args += ["-object", "ot-rom_img,id=rom,file={}".format(firmware.rom.short_path)]

    qemu_args += ["-drive", "if=pflash,file=otp_img.raw,format=raw"]
    test_script_fmt |= {
        "mutable_otp": "otp_img.raw",
        "otp": firmware.otp.short_path,
    }

    if firmware.signed_bin != None and firmware.binary != None:
        qemu_args += ["-drive", "if=mtd,id=eflash,bus=2,file=flash_img.bin,format=raw"]
        test_script_fmt |= {
            "flash": firmware.default.short_path,
            "mutable_flash": "flash_img.bin",
        }
    else:
        test_script_fmt |= {
            "flash": "",
            "mutable_flash": "",
        }

    # Forward UART0 to stdout.
    qemu_args += ["-chardev", "stdio,id=serial0"]
    qemu_args += ["-serial", "chardev:serial0"]

    # Scale the Ibex clock by an `icount` factor.
    qemu_args += ["-icount", "shift={}".format(param["icount"])]

    # Quit QEMU immediately on rstmgr fatal resets by default.
    qemu_args += ["-global", "ot-rstmgr.fatal_reset=1"]

    # Add parameter-specified globals.
    if param["globals"]:
        globals = json.decode(param["globals"])
        for key, val in globals.items():
            qemu_args += ["-global", "{}={}".format(key, val)]

    args += " " + " ".join(qemu_args)

    # Construct the test script
    script = ctx.actions.declare_file(ctx.attr.name + ".bash")

    post_test_harness_path = ctx.executable.post_test_harness
    post_test_cmd = ctx.attr.post_test_cmd.format(**param)

    if post_test_harness_path != None:
        data_files.append(post_test_harness_path)
        post_test_harness_path = post_test_harness_path.short_path
    else:
        post_test_harness_path = ""

    ctx.actions.write(
        script,
        _TEST_SCRIPT.format(
            test_harness = test_harness.executable.short_path,
            args = args,
            post_test_harness = post_test_harness_path,
            post_test_cmd = post_test_cmd,
            **test_script_fmt
        ),
    )

    return script, data_files
