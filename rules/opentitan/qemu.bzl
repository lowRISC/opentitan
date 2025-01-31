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

function cleanup {{
  echo "cleanup: {post_test_harness} {post_test_cmd}"
  {post_test_harness} {post_test_cmd}
}}

# Bazel will send a SIGTERM when the timeout expires and will
# wait for a short amount of time (local_termination_grace_seconds)
# before it kills the process. Therefore the trap will run even
# on timeout.
trap cleanup EXIT

# QEMU requires mutable flash and OTP files but Bazel only provides RO
# files so we have to create copies unique to this test run.
cp {flash} {mutable_flash}
cp {otp} {mutable_otp}
chmod +w {mutable_flash} {mutable_otp}

mkfifo stdout

# Spawn QEMU in the background but `tee` its stdout to a named pipe.
echo Invoking test: {test_harness} {args} "$@"
RUST_BACKTRACE=1 {test_harness} {args} "$@" | tee stdout &

# Wait for `PASS!` message to indicate success.
# Note: `FAIL!` meesages will not immediately fail the test, they will
# have to wait for timeout. This will be fixed when QEMU is executed
# through `opentitantool.`
grep -m1 -q 'PASS!' stdout
"""

def qemu_params(
        tags = [],
        timeout = "short",
        local = True,
        test_harness = "//third_party/qemu:qemu-system-riscv32",
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
        "extra_args": " ".join(["-global {}={}".format(key, val) for (key, val) in globals.items()]),
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

def gen_flash(ctx, **kwargs):
    name = get_override(ctx, "label.name", kwargs)
    out = ctx.actions.declare_file(name + ".qemu_bin")

    app = get_override(ctx, "file.app", kwargs)
    app_elf = get_override(ctx, "file.app_elf", kwargs)

    flashgen = get_override(ctx, "executable.flashgen", kwargs)

    ctx.actions.run(
        inputs = [app, app_elf],
        outputs = [out],
        executable = flashgen[DefaultInfo].files_to_run,
        arguments = [
            "-x",
            app.path,
            "-X",
            app_elf.path,
            out.path,
        ],
        mnemonic = "FlashGen",
    )
    return out

qemu_flash = rule(
    implementation = lambda ctx: [DefaultInfo(files = depset([gen_flash(ctx)]))],
    attrs = {
        "app": attr.label(allow_single_file = True),
        "app_elf": attr.label(allow_single_file = True),
        "bank": attr.string(default = "0"),
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
            app = signed_bin,
            app_elf = elf,
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

    mutable_otp = "otp_img.raw"
    mutable_flash = "flash_img.bin"

    qemu_args = []
    qemu_args += ["-display", "none"]
    qemu_args += ["-M", "ot-{}".format(exec_env.design)]

    # Provide top-spe
    qemu_args += ["-readconfig", "{}".format(firmware.qemu_cfg.short_path)]
    qemu_args += ["-object", "ot-rom_img,id=rom,file={}".format(firmware.rom.short_path)]
    qemu_args += ["-drive", "if=pflash,file={},format=raw".format(mutable_otp)]
    qemu_args += ["-drive", "if=mtd,bus=1,file={},format=raw".format(mutable_flash)]

    # Forward UART0 to stdout.
    qemu_args += ["-chardev", "stdio,id=serial0"]
    qemu_args += ["-serial", "chardev:serial0"]

    # Scale the Ibex clock by an `icount` factor.
    qemu_args += ["-icount", "shift={}".format(param["icount"])]

    # Quit QEMU immediately on rstmgr fatal resets.
    qemu_args += ["-global", "ot-rstmgr.fatal_reset=1"]

    data_files += [firmware.qemu_cfg, firmware.otp]

    # Get the pre-test_cmd args.
    args = get_fallback(ctx, "attr.args", exec_env)
    args = " ".join(args + qemu_args).format(**param)
    args = ctx.expand_location(args, data_labels)

    # Extra arguments including globals.
    if param["extra_args"] and len(param["extra_args"]) > 0:
        args += " " + param["extra_args"]

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
            otp = firmware.otp.short_path,
            mutable_otp = mutable_otp,
            flash = firmware.default.short_path,
            mutable_flash = mutable_flash,
        ),
    )

    return script, data_files
