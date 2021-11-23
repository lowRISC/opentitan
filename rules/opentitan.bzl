# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# TODO(drewmacrae) this should be in rules_cc
# pending resolution of https://github.com/bazelbuild/rules_cc/issues/75
load("//rules:bugfix.bzl", "find_cc_toolchain")

"""Rules to build OpenTitan for the RiscV target"""

OPENTITAN_CPU = "@bazel_embedded//constraints/cpu:riscv32"
OPENTITAN_PLATFORM = "@bazel_embedded//platforms:opentitan_rv32imc"

_targets_compatible_with = {
    OPENTITAN_PLATFORM: [OPENTITAN_CPU],
}

def _platforms_transition_impl(settings, attr):
    return {"//command_line_option:platforms": attr.platform}

_platforms_transition = transition(
    implementation = _platforms_transition_impl,
    inputs = [],
    outputs = ["//command_line_option:platforms"],
)

def _obj_transform(ctx):
    cc_toolchain = find_cc_toolchain(ctx)
    outputs = []
    for src in ctx.files.srcs:
        binary = ctx.actions.declare_file("{}.{}".format(src.basename, ctx.attr.suffix))
        outputs.append(binary)
        ctx.actions.run(
            outputs = [binary],
            inputs = [src] + cc_toolchain.all_files.to_list(),
            arguments = [
                "--output-target",
                ctx.attr.format,
                src.path,
                binary.path,
            ],
            executable = cc_toolchain.objcopy_executable,
        )
    return [DefaultInfo(files = depset(outputs), data_runfiles = ctx.runfiles(files = outputs))]

obj_transform = rule(
    implementation = _obj_transform,
    cfg = _platforms_transition,
    attrs = {
        "srcs": attr.label_list(allow_files = True),
        "suffix": attr.string(default = "bin"),
        "format": attr.string(default = "binary"),
        "platform": attr.string(default = OPENTITAN_PLATFORM),
        "_cc_toolchain": attr.label(default = Label("@bazel_tools//tools/cpp:current_cc_toolchain")),
        "_allowlist_function_transition": attr.label(
            default = "@bazel_tools//tools/allowlists/function_transition_allowlist",
        ),
    },
    toolchains = ["@rules_cc//cc:toolchain_type"],
)

def _elf_to_disassembly(ctx):
    cc_toolchain = find_cc_toolchain(ctx)
    outputs = []
    for src in ctx.files.srcs:
        disassembly = ctx.actions.declare_file("{}.dis".format(src.basename))
        outputs.append(disassembly)
        ctx.actions.run_shell(
            outputs = [disassembly],
            inputs = [src] + cc_toolchain.all_files.to_list(),
            arguments = [
                cc_toolchain.objdump_executable,
                src.path,
                disassembly.path,
            ],
            command = "$1 --disassemble --headers --line-numbers --source $2 > $3",
        )
        return [DefaultInfo(files = depset(outputs), data_runfiles = ctx.runfiles(files = outputs))]

elf_to_disassembly = rule(
    implementation = _elf_to_disassembly,
    cfg = _platforms_transition,
    attrs = {
        "srcs": attr.label_list(allow_files = True),
        "platform": attr.string(default = OPENTITAN_PLATFORM),
        "_cc_toolchain": attr.label(default = Label("@bazel_tools//tools/cpp:current_cc_toolchain")),
        "_allowlist_function_transition": attr.label(
            default = "@bazel_tools//tools/allowlists/function_transition_allowlist",
        ),
    },
    toolchains = ["@rules_cc//cc:toolchain_type"],
    incompatible_use_toolchain_transition = True,
)

def _elf_to_scrambled(ctx):
    outputs = []
    for src in ctx.files.srcs:
        scrambled = ctx.actions.declare_file("{}.scr.40.vmem".format(src.basename))
        outputs.append(scrambled)
        ctx.actions.run(
            outputs = [scrambled],
            inputs = [
                src,
                ctx.files._tool[0],
                ctx.files._config[0],
            ],
            arguments = [
                ctx.files._config[0].path,
                src.path,
                scrambled.path,
            ],
            executable = ctx.files._tool[0].path,
        )
        return [DefaultInfo(files = depset(outputs), data_runfiles = ctx.runfiles(files = outputs))]

elf_to_scrambled = rule(
    implementation = _elf_to_scrambled,
    cfg = _platforms_transition,
    attrs = {
        "srcs": attr.label_list(allow_files = True),
        "platform": attr.string(default = OPENTITAN_PLATFORM),
        "_tool": attr.label(default = "//hw/ip/rom_ctrl/util:scramble_image.py", allow_files = True),
        "_config": attr.label(default = "//hw/top_earlgrey/data:autogen/top_earlgrey.gen.hjson", allow_files = True),
        "_allowlist_function_transition": attr.label(
            default = "@bazel_tools//tools/allowlists/function_transition_allowlist",
        ),
    },
)

def opentitan_binary(
        name,
        platform = OPENTITAN_PLATFORM,
        per_device_deps = {
            "verilator": ["//sw/device/lib/arch:sim_verilator"],
            "dv": ["//sw/device/lib/arch:sim_dv"],
            "fpga_nexysvideo": ["//sw/device/lib/arch:fpga_nexysvideo"],
            "cw310": ["//sw/device/lib/arch:fpga_cw310"],
        },
        output_bin = True,
        output_disassembly = True,
        output_scrambled = False,
        **kwargs):
    """A helper macro for generating OpenTitan binary artifacts.
    This macro is mostly a wrapper around cc_binary, but creates artifacts
    for each of the keys in `per_device_deps`.  The actual artifacts
    created are an ELF file, a BIN file, the disassembly and the scrambled
    ROM image.  Each of these output targets performs a bazel transition to
    the RV32I toolchain to build the target under the correct compiler.
    Args:
      @param name: The name of this rule.
      @param platform: The target platform for the artifacts.
      @param per_device_deps: The deps for each of the execution environments.
      @param output_bin: Whether or not to emit a BIN file.
      @param output_disassembly: Whether or not to emit a disassembly file.
      @param output_scrambled: Whether or not to emit a SCR file.
      @param **kwargs: Arguments to forward to `cc_binary`.
    Emits rules:
      For each device in per_device_deps entry:
        cc_binary     named: name_device
        obj_transform named: name_device_elf
        optionally:
          obj_transform       named: name_device_bin
          elf_to_dissassembly named: name_device_dis
          elf_to_scrambled    named: name_device_scr
      filegroup named: name
          with all the generated rules
    """

    copts = kwargs.pop("copts", []) + [
        "-nostdlib",
        "-ffreestanding",
    ]
    linkopts = kwargs.pop("linkopts", []) + [
        "-nostartfiles",
        "-nostdlib",
    ]
    deps = kwargs.pop("deps", [])
    targets = []
    for (device, dev_deps) in per_device_deps.items():
        devname = "{}_{}".format(name, device)
        native.cc_binary(
            name = devname,
            deps = deps + dev_deps,
            target_compatible_with = _targets_compatible_with[platform],
            copts = copts,
            linkopts = linkopts,
            **kwargs
        )
        targets.append(":" + devname + "_elf")
        obj_transform(
            name = devname + "_elf",
            srcs = [devname],
            format = "elf32-little",
            suffix = "elf",
            platform = platform,
        )

        if output_bin:
            targets.append(":" + devname + "_bin")
            obj_transform(
                name = devname + "_bin",
                srcs = [devname],
                platform = platform,
            )

        if output_disassembly:
            targets.append(":" + devname + "_dis")
            elf_to_disassembly(
                name = devname + "_dis",
                srcs = [devname],
                platform = platform,
            )
        if output_scrambled:
            targets.append(":" + devname + "_scr")
            elf_to_scrambled(
                name = devname + "_scr",
                srcs = [devname],
                platform = platform,
            )

    native.filegroup(
        name = name,
        srcs = targets,
    )

def verilator_params(
        rom = "//sw/device/boot_rom:boot_rom_verilator_scr",
        otp = "//hw/ip/otp_ctrl/data:rma_image_verilator",
        tags = ["verilator"],
        timeout = "moderate",
        local = True,
        args = [],
        data = [],
        **kwargs):
    kwargs.update(rom=rom, otp=otp, tags=tags, timeout=timeout, local=local, args=args, data=data)
    return kwargs

def cw310_params(
        tags = ["cw310"],
        timeout = "moderate",
        local = True,
        args = [],
        data = [],
        **kwargs):
    kwargs.update(tags=tags, timeout=timeout, local=local, args=args, data=data)
    return kwargs

def opentitan_functest(
        name,
        platform = OPENTITAN_PLATFORM,
        targets = ["verilator", "cw310"],
        args = [],
        data = [],
        verilator = None,
        cw310 = None,
        **kwargs):
    """A helper macro for generating OpenTitan functional tests.
    This macro is mostly a wrapper around opentitan_binary, but creates
    testing artifacts for each of the keys in `per_device_deps`.
    The testing artifacts are then given to an `sh_test` rule which
    dispatches the test via opentitantool.
    Args:
      @param name: The name of this rule.
      @param platform: The target platform for the artifacts.
      @param targets: A list of targets on which to dispatch tests.
      @param args: Extra arguments to pass to `opentitantool_test_runner.sh`.
      @param data: Extra data dependencies needed while executing the test.
      @param **kwargs: Arguments to forward to `opentitan_binary`.

    This macro emits the following rules:
        opentitan_binary named: {name}_prog (and all of its emitted rules).
        sh_test named:          {name}_verilator_{test suffix}
        sh_test named:          {name}_cw310_{test suffix}
        test_suite named:       {name}
    """

    opentitan_binary(
        name = name + "_prog",
        platform = platform,
        output_disassembly = False,
        **kwargs
    )

    n = name.split("_")
    n.insert(-1, "{}")
    testname_fmt = "_".join(n)
    all_tests = []

    if "verilator" in targets:
        test_name = testname_fmt.format("verilator")
        test_bin = "{}_prog_verilator_elf".format(name)
        all_tests.append(test_name)

        if verilator == None:
            verilator = verilator_params()
        rom = verilator.pop("rom")
        otp = verilator.pop("otp")
        vargs = args + verilator.pop("args", [])
        vdata = data + verilator.pop("data", [])

        native.sh_test(
            name = test_name,
            srcs = ["//util:opentitantool_test_runner.sh"],
            args = [
                "--interface=verilator",
                "--test-bin=$(location {})".format(test_bin),
                "--verilator-dir=$(location //hw:verilator)",
                "--verilator-rom=$(location {})".format(rom),
                "--verilator-otp=$(location {})".format(otp),
            ] + vargs,
            data = [
                test_bin,
                rom,
                otp,
                "//sw/host/opentitantool:test_resources",
                "//hw:verilator",
            ] + vdata,
            **verilator,
        )

    if "cw310" in targets:
        test_name = testname_fmt.format("cw310")
        test_bin = "{}_prog_cw310_bin".format(name)
        all_tests.append(test_name)

        if cw310 == None:
            cw310 = cw310_params()
        cargs = args + cw310.pop("args", [])
        cdata = data + cw310.pop("data", [])

        native.sh_test(
            name = test_name,
            srcs = ["//util:opentitantool_test_runner.sh"],
            args = [
                "--interface=cw310",
                "--test-bin=$(location {})".format(test_bin),
            ] + cargs,
            data = [
                test_bin,
                "//sw/host/opentitantool:test_resources",
            ] + cdata,
            **cw310,
        )

    native.test_suite(
        name = name,
        tests = all_tests,
    )
