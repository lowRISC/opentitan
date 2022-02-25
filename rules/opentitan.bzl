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

def _opentitan_transition_impl(settings, attr):
    return {"//command_line_option:platforms": attr.platform}

opentitan_transition = transition(
    implementation = _opentitan_transition_impl,
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
    cfg = opentitan_transition,
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

def _sign_image_impl(ctx):
    outputs = []
    signed_image = ctx.actions.declare_file(
        "{0}.{1}.signed.bin".format(
            ctx.file.bin.basename.rstrip(".bin"),
            ctx.attr.key_name,
        ),
    )
    outputs.append(signed_image)
    ctx.actions.run(
        outputs = [signed_image],
        inputs = [
            ctx.file.bin,
            ctx.file.elf,
            ctx.file.key,
            ctx.file._tool,
        ],
        arguments = [
            "rom_ext",
            ctx.file.bin.path,
            ctx.file.key.path,
            ctx.file.elf.path,
            signed_image.path,
        ],
        executable = ctx.file._tool.path,
    )
    return [DefaultInfo(
        files = depset(outputs),
        data_runfiles = ctx.runfiles(files = outputs),
    )]

sign_image = rule(
    implementation = _sign_image_impl,
    cfg = opentitan_transition,
    attrs = {
        "bin": attr.label(allow_single_file = True),
        "elf": attr.label(allow_single_file = True),
        "key": attr.label(
            default = "//sw/device/silicon_creator/mask_rom/keys:test_private_key_0",
            allow_single_file = True,
        ),
        "key_name": attr.string(),
        "platform": attr.string(default = "@local_config_platform//:host"),
        "_tool": attr.label(
            default = "//sw/host/rom_ext_image_tools/signer:rom_ext_signer",
            allow_single_file = True,
        ),
        "_allowlist_function_transition": attr.label(
            default = "@bazel_tools//tools/allowlists/function_transition_allowlist",
        ),
    },
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
    cfg = opentitan_transition,
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
    cfg = opentitan_transition,
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
        signing_keys = {
            "test_key_0": "//sw/device/silicon_creator/mask_rom/keys:test_private_key_0",
        },
        output_bin = True,
        output_disassembly = True,
        output_signed = False,
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
      @param output_signed: Whether or not to emit a signed binary.
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

        if output_signed:
            for (key_name, key) in signing_keys.items():
                targets.append(":" + devname + "_bin_signed_" + key_name)
                sign_image(
                    name = devname + "_bin_signed_" + key_name,
                    bin = devname + "_bin",
                    elf = devname + "_elf",
                    key = key,
                    key_name = key_name,
                )

    native.filegroup(
        name = name,
        srcs = targets,
    )

def verilator_params(
        rom = "//sw/device/lib/testing/test_rom:test_rom_verilator_scr",
        otp = "//hw/ip/otp_ctrl/data:rma_image_verilator",
        tags = [
            "cpu:4",
        ],
        timeout = "moderate",
        local = True,
        args = [
            "console",
            "--exit-failure=FAIL",
            "--exit-success=PASS",
            "--timeout=3600",
        ],
        data = [],
        **kwargs):
    """A macro to create verilator parameters for OpenTitan functional tests.

    This macro emits a dictionary of parameters which are pasted into the
    verilator specific test rule.

    Args:
        @param rom: The ROM to use when booting verilator.
        @param otp: The OTP image to use when booting verilator.
        @param tags: The test tags to apply to the test rule.
        @param timeout: The timeout to apply to the test rule.
        @param local: Whether the test should be run locally and without sandboxing.
        @param args: Arguments to pass to the test.
        @param data: Data dependencies of the test.
    """
    kwargs.update(rom = rom, otp = otp, tags = tags + ["verilator"], timeout = timeout, local = local, args = args, data = data)
    return kwargs

def cw310_params(
        tags = [],
        timeout = "moderate",
        local = True,
        args = [
            "--exec=\"console -q -t0\"",
            "--exec=\"bootstrap $(location {test_bin})\"",
            "console",
            "--exit-failure=FAIL",
            "--exit-success=PASS",
            "--timeout=3600",
        ],
        data = [],
        **kwargs):
    """A macro to create CW310 parameters for OpenTitan functional tests.

    This macro emits a dictionary of parameters which are pasted into the
    ChipWhisperer-310 specific test rule.

    Args:
        @param tags: The test tags to apply to the test rule.
        @param timeout: The timeout to apply to the test rule.
        @param local: Whether the test should be run locally and without sandboxing.
        @param args: Arguments to pass to the test.
        @param data: Data dependencies of the test.
    """
    kwargs.update(tags = tags + ["cw310", "exclusive"], timeout = timeout, local = local, args = args, data = data)
    return kwargs

def _format_list(name, list1, datadict, **kwargs):
    """Concatenate and format list items.

    This is used to prepare substitutions in user-supplied args to the
    various test invocations (ie: the location of test_bin).
    Args:
        @param name: The name of the item in `datadict`.
        @param list1: A list of items to prepend to the list item from datadict.
        @param datadict: A dictionary of per-test parameters.
        @param **kwargs: Values to pass to the format function.
    Returns:
        list[str]
    """
    return [x.format(**kwargs) for x in list1 + datadict.pop(name, [])]

_OTTF_DEPS = [
    "//sw/device/lib/arch:device",
    "//sw/device/lib/base",
    "//sw/device/lib/runtime:hart",
    "//sw/device/lib/runtime:log",
    "//sw/device/lib/runtime:print",
    "//sw/device/lib/crt",
    "//sw/device/lib/testing/test_framework:ottf_start",
    "//sw/device/lib/testing/test_framework:ottf",
    "//sw/device/lib/base:mmio",
]

def _unique_deps(*deplists):
    uniq = {}
    for deplist in deplists:
        for dep in deplist:
            uniq[dep] = True
    return uniq.keys()

def opentitan_functest(
        name,
        platform = OPENTITAN_PLATFORM,
        targets = ["verilator", "cw310"],
        args = [],
        data = [],
        ottf = _OTTF_DEPS,
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
      @param args: Extra arguments to pass to `opentitantool`.
      @param data: Extra data dependencies needed while executing the test.
      @param ottf: Default dependencies for OTTF tests.  Set to empty list if
                   your test doesn't use the OTTF.
      @param **kwargs: Arguments to forward to `opentitan_binary`.

    This macro emits the following rules:
        opentitan_binary named: {name}_prog (and all of its emitted rules).
        sh_test named:          verilator_{name}
        sh_test named:          cw310_{name}
        test_suite named:       {name}
    """

    deps = _unique_deps(kwargs.pop("deps", []), ottf)
    opentitan_binary(
        name = name + "_prog",
        platform = platform,
        output_disassembly = True,
        deps = deps,
        **kwargs
    )

    all_tests = []

    if "verilator" in targets:
        test_name = "verilator_{}".format(name)
        test_bin = "{}_prog_verilator_elf".format(name)

        if verilator == None:
            verilator = verilator_params()
        rom = verilator.pop("rom")
        otp = verilator.pop("otp")
        vargs = _format_list("args", args, verilator, test_bin = test_bin)
        vdata = _format_list("data", data, verilator, test_bin = test_bin)

        if "manual" not in verilator.get("tags", []):
            all_tests.append(test_name)

        native.sh_test(
            name = test_name,
            srcs = ["//util:opentitantool_test_runner.sh"],
            args = [
                "--rcfile=",
                "--logging=info",
                "--interface=verilator",
                "--conf=sw/host/opentitantool/config/opentitan_verilator.json",
                "--verilator-bin=$(location //hw:verilator)/sim-verilator/Vchip_sim_tb",
                "--verilator-rom=$(location {})".format(rom),
                "--verilator-flash=$(location {})".format(test_bin),
                "--verilator-otp=$(location {})".format(otp),
            ] + vargs,
            data = [
                test_bin,
                rom,
                otp,
                "//sw/host/opentitantool:test_resources",
                "//hw:verilator",
            ] + vdata,
            **verilator
        )

    if "cw310" in targets:
        test_name = "cw310_{}".format(name)
        test_bin = "{}_prog_cw310_bin".format(name)

        if cw310 == None:
            cw310 = cw310_params()
        cargs = _format_list("args", args, cw310, test_bin = test_bin)
        cdata = _format_list("data", data, cw310, test_bin = test_bin)

        if "manual" not in cw310.get("tags", []):
            all_tests.append(test_name)

        native.sh_test(
            name = test_name,
            srcs = ["//util:opentitantool_test_runner.sh"],
            args = [
                "--rcfile=",
                "--logging=info",
                "--interface=cw310",
                "--conf=sw/host/opentitantool/config/opentitan_cw310.json",
            ] + cargs,
            data = [
                test_bin,
                "//sw/host/opentitantool:test_resources",
            ] + cdata,
            **cw310
        )

    native.test_suite(
        name = name,
        tests = all_tests,
    )
