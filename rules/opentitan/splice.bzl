# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:exec_env.bzl", "ExecEnvInfo")
load("//rules/opentitan:providers.bzl", "get_one_binary_file")
load("//rules/opentitan:toolchain.bzl", "LOCALTOOLS_TOOLCHAIN")
load("//rules/opentitan:util.bzl", "get_fallback")
load("@nonhermetic//:env.bzl", "ENV")

# Rules for memory splicing with Vivado.

DEFAULTS = struct(
    rom = "//hw/bitstream/universal:none",
    otp = "//hw/bitstream/universal:none",
    env = "//hw/bitstream/universal:none",
)

def gen_vivado_mem_file(ctx, name, src, tool, swap_nibbles = True):
    update = ctx.actions.declare_file("{}.update.mem".format(name))
    args = ctx.actions.args()
    if swap_nibbles:
        args.add("--swap-nibbles")
    args.add_all([src, update])
    ctx.actions.run(
        mnemonic = "GenVivadoImage",
        outputs = [update],
        inputs = [src],
        arguments = [args],
        executable = tool,
        use_default_shell_env = True,
        execution_requirements = {
            "no-sandbox": "",
        },
    )
    return update

def vivado_updatemem(ctx, name, src, mmi, update, debug = False):
    spliced = ctx.actions.declare_file("{}.bit".format(name))

    # Vivado's `updatemem` only accepts bitstream filenames that end with `.bit`.
    # If the filename doesn't have that extension, symlink to a name that does.
    if src.extension != "bit":
        tmpsrc = ctx.actions.declare_file("{}.tmpsrc.bit".format(name))
        ctx.actions.symlink(output = tmpsrc, target_file = src)
        src = tmpsrc

    args = ctx.actions.args()
    if debug:
        args.add("--debug")
    args.add("--force")
    args.add("--meminfo", mmi)
    args.add("--data", update)
    args.add("--bit", src)
    args.add("--proc", "dummy")
    args.add("--out", spliced)

    ctx.actions.run(
        mnemonic = "SpliceBitstream",
        outputs = [spliced],
        inputs = [src, mmi, update],
        arguments = [args],
        executable = "updatemem",
        use_default_shell_env = False,
        execution_requirements = {
            "no-sandbox": "",
        },
        env = ENV,
    )
    return spliced

def update_usr_access(ctx, name, src, tool):
    """Updates the USR_ACCESS value in the bistream.

    Updating the USR_ACCESS gives each spliced bitstream a unique value that
    can be printed out by the ROM so that test tools can determine if they are
    running with the correct bitstream for that test.
    """
    output = ctx.actions.declare_file("{}.bit".format(name))
    args = ctx.actions.args()
    args.add_all([
        "--rcfile=",
        "fpga",
        "update-usr-access",
        src,
        output,
    ])
    ctx.actions.run(
        mnemonic = "UpdateUsrAccessValue",
        outputs = [output],
        inputs = [src],
        arguments = [args],
        executable = tool,
    )
    return output

def _bitstream_splice_impl(ctx):
    tc = ctx.toolchains[LOCALTOOLS_TOOLCHAIN]
    if ctx.attr.exec_env.label.name == "none":
        # This is required so that this rule won't fail in bazel queries.
        print("{}: No exec_env.  Nothing to do.".format(ctx.label))
        return DefaultInfo()
    if ExecEnvInfo not in ctx.attr.exec_env:
        fail("Not an exec_env:", ctx.attr.exec_env.label)

    exec_env = ctx.attr.exec_env[ExecEnvInfo]
    src = ctx.file.src if ctx.file.src else exec_env.base_bitstream

    # Splice in a ROM image if we have one either in attrs or the exec_env.
    if not ctx.attr.rom or ctx.attr.rom.label.name == "none":
        rom = exec_env.rom
    else:
        rom = ctx.attr.rom
    if rom and rom.label.name != "none":
        rom = get_one_binary_file(rom, field = "rom", providers = [exec_env.provider])
        mem = gen_vivado_mem_file(
            ctx = ctx,
            name = "{}-rom".format(ctx.label.name),
            src = rom,
            tool = tc.tools.gen_mem_image,
            swap_nibbles = ctx.attr.swap_nibbles,
        )
        src = vivado_updatemem(
            ctx = ctx,
            name = "{}-rom".format(ctx.label.name),
            src = src,
            mmi = get_fallback(ctx, "file.rom_mmi", exec_env),
            update = mem,
            debug = ctx.attr.debug,
        )

    # Splice in an OTP image if we have one either in attrs or the exec_env.
    if not ctx.attr.otp or ctx.attr.otp.label.name == "none":
        otp = exec_env.otp
    else:
        otp = ctx.file.otp
    if otp:
        mem = gen_vivado_mem_file(
            ctx = ctx,
            name = "{}-otp".format(ctx.label.name),
            src = otp,
            tool = tc.tools.gen_mem_image,
            swap_nibbles = ctx.attr.swap_nibbles,
        )
        src = vivado_updatemem(
            ctx = ctx,
            name = "{}-otp".format(ctx.label.name),
            src = src,
            mmi = get_fallback(ctx, "file.otp_mmi", exec_env),
            update = mem,
            debug = ctx.attr.debug,
        )

    output = update_usr_access(
        ctx = ctx,
        name = ctx.label.name,
        src = src,
        tool = tc.tools.opentitantool,
    )
    return DefaultInfo(files = depset([output]))

bitstream_splice = rule(
    implementation = _bitstream_splice_impl,
    attrs = {
        "src": attr.label(allow_single_file = True, doc = "The bitstream to splice"),
        "otp": attr.label(allow_single_file = True, doc = "The OTP image to splice into the bitstream"),
        "otp_mmi": attr.label(allow_single_file = True, doc = "The OTP meminfo file"),
        "rom": attr.label(doc = "The ROM image to splice into the bitstream"),
        "rom_mmi": attr.label(allow_single_file = True, doc = "The ROM meminfo file"),
        "exec_env": attr.label(providers = [[ExecEnvInfo], [DefaultInfo]], mandatory = True, doc = "The exec_env to splice for"),
        "swap_nibbles": attr.bool(default = True, doc = "Swap nybbles while preparing the memory image"),
        "debug": attr.bool(default = False, doc = "Emit debug info while updating"),
    },
    toolchains = [LOCALTOOLS_TOOLCHAIN],
)
