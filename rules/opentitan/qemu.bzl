# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "@lowrisc_opentitan//rules/opentitan:providers.bzl",
    "SimQemuBinaryInfo",
)
load(
    "@lowrisc_opentitan//rules/opentitan:util.bzl",
    "assemble_for_test",
    "get_fallback",
    "get_override",
    "recursive_format",
)
load(
    "//rules/opentitan:exec_env.bzl",
    "ExecEnvInfo",
    "common_test_setup",
    "exec_env_as_dict",
    "exec_env_common_attrs",
)
load("//rules/opentitan:toolchain.bzl", "LOCALTOOLS_TOOLCHAIN")

def qemu_params(
        tags = [],
        timeout = "short",
        local = True,
        test_harness = None,
        binaries = {},
        rom = None,
        rom_ext = None,
        otp = None,
        bitstream = None,
        needs_jtag = False,
        test_cmd = "",
        data = [],
        defines = [],
        icount = 6,
        globals = {},
        traces = [],
        qemu_args = [],
        bootstrap = False,
        **kwargs):
    extra_params = {
        "icount": str(icount),
        "qemu_args": json.encode(qemu_args),
        # We have to stringify this dictionary here because `_opentitan_test` only accepts
        # a dict with string values, not more dicts.
        "globals": json.encode(globals),
        # The same goes for this array of strings:
        "traces": json.encode(traces),
        # And these Booleans:
        "bootstrap": json.encode(bootstrap),
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
        test_cmd = ("""
            {jtag_test_cmd}
        """ if needs_jtag else "") + test_cmd,
        data = data,
        param = kwargs | extra_params,
        defines = defines,
        needs_jtag = needs_jtag,
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

    check_elfs = get_override(ctx, "file.check_elfs", kwargs)

    flashgen = get_override(ctx, "executable.flashgen", kwargs)

    flashgen_inputs = []
    flashgen_args = []

    # Add the firmware binary, which will be placed at 0x0 and as such
    # should contain relevant padding to offset from the start of flash.
    # Firmware binaries can be placed across flash banks, i.e. they can
    # be mirrored.
    if firmware_bin:
        flashgen_inputs += [firmware_bin]
        flashgen_args += ["-t", "{}@0x0".format(firmware_bin.path)]
        # TODO: currently firmware_elf is unused due to lacking support in QEMU

    if check_elfs:
        # Skip `flashgen`'s ELF/binary mtime checks - it will fail if the
        # binary is older than the ELF which usually suggests that the
        # binary has not been regenerated, however Bazel often messes with
        # mtimes causing false negatives.
        flashgen_args += ["--ignore-time"]
    else:
        flashgen_args += ["--unsafe-elf"]

    flashgen_args += [out.path]

    ctx.actions.run(
        inputs = flashgen_inputs,
        outputs = [out],
        executable = flashgen[DefaultInfo].files_to_run,
        arguments = flashgen_args,
        mnemonic = "FlashGen",
    )
    return out

qemu_flash = rule(
    implementation = lambda ctx: [DefaultInfo(files = depset([gen_flash(ctx)]))],
    attrs = {
        "firmware_bin": attr.label(
            allow_single_file = True,
            doc = "Binary firmware to be run after the ROM, usually signed, placed at the start of flash",
        ),
        "firmware_elf": attr.label(
            allow_single_file = True,
            doc = "ELF version of the `firmware_bin` attribute for symbol tracking",
        ),
        "check_elfs": attr.bool(
            default = True,
            doc = "Whether to sanity check ELF sizes against binaries. Should be `false` if using signed binaries",
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
        qemu = ctx.executable.qemu,
        qemu_start = ctx.executable._qemu_start,
        cfggen = ctx.attr.cfggen,
        otptool = ctx.attr.otptool,
        flashgen = ctx.attr.flashgen,
        otp_sv = ctx.file.otp_sv,
        lc_sv = ctx.file.lc_sv,
        top_hjson = ctx.file.top_hjson,
        test_script = ctx.file._test_script,
        **fields
    )

sim_qemu = rule(
    implementation = _sim_qemu,
    attrs = exec_env_common_attrs() | {
        "opentitantool": attr.label(
            executable = True,
            cfg = "exec",
            default = Label("//sw/host/opentitantool"),
        ),
        "qemu": attr.label(
            executable = True,
            cfg = "exec",
            allow_files = True,
            default = Label("//third_party/qemu:qemu-system-riscv32"),
        ),
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
            default = Label("//hw/ip/otp_ctrl:rtl/otp_ctrl_part_pkg.sv"),
        ),
        "lc_sv": attr.label(
            allow_single_file = True,
            default = Label("//hw/ip/lc_ctrl:rtl/lc_ctrl_state_pkg.sv"),
        ),
        "top_hjson": attr.label(
            allow_single_file = True,
            default = Label("//hw/top_earlgrey/data:autogen/top_earlgrey.gen.hjson"),
        ),
        "_qemu_start": attr.label(
            executable = True,
            cfg = "exec",
            default = "//hw/top_earlgrey/sw/util:qemu_start",
        ),
        "_test_script": attr.label(
            allow_single_file = True,
            default = "//rules/scripts:qemu_test.sh",
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
        default = signed_bin if signed_bin else binary
        rom = None
    else:
        fail("Not implemented: kind == ", ctx.attr.kind)

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

    # If the test requested an assembled image, then use opentitantool to
    # assemble the image.
    if "assemble" in param:
        assemble = param.get("assemble")
        assemble = recursive_format(assemble, action_param)
        assemble = ctx.expand_location(assemble, data_labels)
        image = assemble_for_test(
            ctx,
            name = ctx.attr.name,
            spec = assemble.strip().split(" "),
            data_files = data_files,
            opentitantool = exec_env._opentitantool,
        )
        data_files.append(image)
    elif firmware:
        image = firmware.signed_bin or firmware.default
    else:
        image = None

    # Replace the firmware param with the newly assembled image.
    if image:
        param["firmware"] = image.short_path
        action_param["firmware"] = image.path

    data_files += [exec_env.qemu, exec_env.qemu_start]

    # Add arguments to pass directly to QEMU.
    test_script_fmt = {}

    # Generate the OpenTitan machine config for QEMU emulation
    qemu_cfg = gen_cfg(
        ctx,
        cfggen = exec_env.cfggen,
        otp_sv = exec_env.otp_sv,
        lc_sv = exec_env.lc_sv,
        top_hjson = exec_env.top_hjson,
        top_name = exec_env.design,
    )
    data_files += [qemu_cfg]

    # Generate the OTP backend image for QEMU emulation
    otp_image = gen_otp(
        ctx,
        otptool = exec_env.otptool,
        vmem = get_fallback(ctx, "file.otp", exec_env),
    )
    data_files += [otp_image]
    test_script_fmt |= {
        "otp": otp_image.short_path,
    }

    # If real bootstrapping is requested then prepare the correct command, otherwise we need
    # to prepare a QEMU drive containing flash contents.
    # Ideally, relevant info pages would be spliced in at this step, but that is
    # not yet supported by either flashgen or by Bazel.
    if param["bootstrap"] and json.decode(param["bootstrap"]):
        if ctx.attr.test_harness:
            fail("cannot specify both `bootstrap = True` and a test harness (harnesses bootstrap manually)")
        test_script_fmt |= {"flash": ""}
        bootstrap_cmd = "bootstrap --clear-uart=true {firmware}".format(**param)
        param["bootstrap_cmd"] = '--exec="{}"'.format(bootstrap_cmd)
    else:
        # Generate the flash backend image for QEMU emulation
        flash_image = gen_flash(
            ctx,
            flashgen = exec_env.flashgen,
            firmware_bin = image,
            # TODO: no support for convenience debug symbols from ELFs for now
            firmware_elf = None,
            # Do not sanity check ELFs, because we do not expect the binary to
            # match the ELF because of the added manifest extensions (e.g. SPX
            # signatures) present in the signed binary.
            check_elfs = False,
        )
        data_files += [flash_image]
        test_script_fmt |= {
            "flash": flash_image.short_path,
        }
        param["bootstrap_cmd"] = '--exec="no-op" # SKIPPING BOOTSTRAP'

    # Get the pre-test_cmd args.
    args = get_fallback(ctx, "attr.args", exec_env)
    args = " ".join(args).format(**param)
    args = ctx.expand_location(args, data_labels)

    # Assemble extra QEMU args from test parameters
    qemu_args = []

    if param["traces"]:
        traces = json.decode(param["traces"])
        for trace in traces:
            qemu_args += ["--trace", "{}".format(trace)]

    # Add parameter-specified globals.
    if param["globals"]:
        globals = json.decode(param["globals"])
        for key, val in globals.items():
            qemu_args += ["-global", "{}={}".format(key, val)]

    if param["qemu_args"]:
        qemu_args += json.decode(param["qemu_args"])

    qemu_args = " ".join(qemu_args)

    # Construct the test script
    script = ctx.actions.declare_file(ctx.attr.name + ".bash")

    # Pair the `test_cmd` with the test harness - if overridden, don't use the
    # default `test_cmd`.
    if ctx.attr.test_harness:
        test_cmd = ctx.attr.test_cmd
    else:
        test_cmd = exec_env.test_cmd
    test_cmd = test_cmd.format(**param)
    test_cmd = ctx.expand_location(test_cmd, data_labels)

    # Pass relevant files through to the test script via templating
    test_script_fmt.update({
        "args": args,
        "config": qemu_cfg.short_path,
        "icount": param["icount"],
        "qemu_args": qemu_args,
        "qemu_bin": exec_env.qemu.short_path,
        "qemu_start": exec_env.qemu_start.short_path,
        "rom": param["rom"],
        "test_cmd": test_cmd,
        "test_harness": test_harness.executable.short_path,
    })
    ctx.actions.expand_template(
        template = exec_env.test_script,
        output = script,
        is_executable = True,
        substitutions = {
            "__" + key + "__": val
            for (key, val) in test_script_fmt.items()
        },
    )

    return script, data_files
