# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_cc//cc:find_cc_toolchain.bzl", "find_cc_toolchain")
load(
    "//rules:cc_side_outputs.bzl",
    "rv_asm",
    "rv_llvm_ir",
    "rv_preprocess",
    "rv_relink_with_linkmap",
)
load(
    "//rules:rv.bzl",
    "rv_rule",
    _OPENTITAN_CPU = "OPENTITAN_CPU",
    _OPENTITAN_PLATFORM = "OPENTITAN_PLATFORM",
    _opentitan_transition = "opentitan_transition",
)

"""Rules to build OpenTitan for the RiscV target"""

# Re-exports of names from transition.bzl; many files in the repo use opentitan.bzl
# to get to them.
OPENTITAN_CPU = _OPENTITAN_CPU
OPENTITAN_PLATFORM = _OPENTITAN_PLATFORM
opentitan_transition = _opentitan_transition

_targets_compatible_with = {
    OPENTITAN_PLATFORM: [OPENTITAN_CPU],
}

# This constant holds a dictionary of per-device dependencies which are used to
# generate slightly different binaries for each hardware target, including two
# simulation platforms (DV and Verilator), and two FPGA platforms (NexysVideo
# and CW310).
PER_DEVICE_DEPS = {
    "sim_verilator": ["//sw/device/lib/arch:sim_verilator"],
    "sim_dv": ["//sw/device/lib/arch:sim_dv"],
    "fpga_cw310": ["//sw/device/lib/arch:fpga_cw310"],
}

def _obj_transform_impl(ctx):
    cc_toolchain = find_cc_toolchain(ctx).cc
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

obj_transform = rv_rule(
    implementation = _obj_transform_impl,
    attrs = {
        "srcs": attr.label_list(allow_files = True),
        "suffix": attr.string(default = "bin"),
        "format": attr.string(default = "binary"),
        "_cc_toolchain": attr.label(default = Label("@bazel_tools//tools/cpp:current_cc_toolchain")),
    },
    toolchains = ["@rules_cc//cc:toolchain_type"],
)

def _sign_bin_impl(ctx):
    outputs = []
    signed_image = ctx.actions.declare_file(
        "{0}.{1}.signed.bin".format(
            # Remove ".bin" from file basename.
            ctx.file.bin.basename.replace("." + ctx.file.bin.extension, ""),
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

sign_bin = rv_rule(
    implementation = _sign_bin_impl,
    attrs = {
        "bin": attr.label(allow_single_file = True),
        "elf": attr.label(allow_single_file = True),
        "key": attr.label(
            default = "//sw/device/silicon_creator/mask_rom/keys:test_private_key_0",
            allow_single_file = True,
        ),
        "key_name": attr.string(),
        # TODO(lowRISC/opentitan:#11199): explore other options to side-step the
        # need for this transition, in order to build the ROM_EXT signer tool.
        "platform": attr.string(default = "@local_config_platform//:host"),
        "_tool": attr.label(
            default = "//sw/host/rom_ext_image_tools/signer:rom_ext_signer",
            allow_single_file = True,
        ),
    },
)

def _elf_to_disassembly_impl(ctx):
    cc_toolchain = find_cc_toolchain(ctx).cc
    outputs = []
    for src in ctx.files.srcs:
        disassembly = ctx.actions.declare_file("{}.elf.s".format(src.basename))
        outputs.append(disassembly)
        ctx.actions.run_shell(
            tools = [ctx.file._cleanup_script],
            outputs = [disassembly],
            inputs = [src] + cc_toolchain.all_files.to_list(),
            arguments = [
                cc_toolchain.objdump_executable,
                src.path,
                ctx.file._cleanup_script.path,
                disassembly.path,
            ],
            command = "$1 --disassemble --headers --line-numbers --disassemble-zeroes --source $2 | $3 > $4",
        )
        return [DefaultInfo(files = depset(outputs), data_runfiles = ctx.runfiles(files = outputs))]

elf_to_disassembly = rv_rule(
    implementation = _elf_to_disassembly_impl,
    attrs = {
        "srcs": attr.label_list(allow_files = True),
        "platform": attr.string(default = OPENTITAN_PLATFORM),
        "_cleanup_script": attr.label(
            allow_single_file = True,
            default = Label("//rules/scripts:expand_tabs.sh"),
        ),
        "_cc_toolchain": attr.label(default = Label("@bazel_tools//tools/cpp:current_cc_toolchain")),
    },
    toolchains = ["@rules_cc//cc:toolchain_type"],
    incompatible_use_toolchain_transition = True,
)

def _elf_to_scrambled_rom_impl(ctx):
    outputs = []
    for src in ctx.files.srcs:
        if src.extension != "elf":
            fail("only ROM images in the ELF format may be converted to the VMEM format and scrambled.")
        scrambled = ctx.actions.declare_file(
            "{}.scr.39.vmem".format(
                # Remove ".elf" from file basename.
                src.basename.replace("." + src.extension, ""),
            ),
        )
        outputs.append(scrambled)
        ctx.actions.run(
            outputs = [scrambled],
            inputs = [
                src,
                ctx.executable._scramble_tool,
                ctx.file._config,
            ],
            arguments = [
                ctx.file._config.path,
                src.path,
                scrambled.path,
            ],
            executable = ctx.executable._scramble_tool,
        )
    return [DefaultInfo(
        files = depset(outputs),
        data_runfiles = ctx.runfiles(files = outputs),
    )]

elf_to_scrambled_rom_vmem = rv_rule(
    implementation = _elf_to_scrambled_rom_impl,
    attrs = {
        "srcs": attr.label_list(allow_files = True),
        "_scramble_tool": attr.label(
            default = "//hw/ip/rom_ctrl/util:scramble_image",
            executable = True,
            cfg = "exec",
        ),
        "_config": attr.label(
            default = "//hw/top_earlgrey/data:autogen/top_earlgrey.gen.hjson",
            allow_single_file = True,
        ),
    },
)

def _bin_to_vmem_impl(ctx):
    outputs = []
    vmem = ctx.actions.declare_file("{}.{}.vmem".format(
        # Remove ".bin" from file basename.
        ctx.file.bin.basename.replace("." + ctx.file.bin.extension, ""),
        ctx.attr.word_size,
    ))
    outputs.append(vmem)
    ctx.actions.run(
        outputs = [vmem],
        inputs = [
            ctx.file.bin,
        ],
        arguments = [
            ctx.file.bin.path,
            "--binary",
            # Reverse the endianness of every word.
            "--offset",
            "0x0",
            "--byte-swap",
            str(ctx.attr.word_size // 8),
            # Pad to word alignment.
            "--fill",
            "0xff",
            "-within",
            ctx.file.bin.path,
            "-binary",
            "-range-pad",
            str(ctx.attr.word_size // 8),
            # Output a VMEM file with specified word size
            "--output",
            vmem.path,
            "--vmem",
            str(ctx.attr.word_size),
        ],
        # This this executable is expected to be installed (as required by the
        # srecord package in apt-requirements.txt).
        executable = "srec_cat",
    )
    return [DefaultInfo(
        files = depset(outputs),
        data_runfiles = ctx.runfiles(files = outputs),
    )]

bin_to_vmem = rv_rule(
    implementation = _bin_to_vmem_impl,
    attrs = {
        "bin": attr.label(allow_single_file = True),
        "word_size": attr.int(
            default = 64,
            doc = "Word size of VMEM file.",
            mandatory = True,
            values = [32, 64],
        ),
    },
)

def _scramble_flash_vmem_impl(ctx):
    outputs = []
    scrambled_vmem = ctx.actions.declare_file("{}.scr.vmem".format(
        # Remove ".vmem" from file basename.
        ctx.file.vmem.basename.replace("." + ctx.file.vmem.extension, ""),
    ))
    outputs.append(scrambled_vmem)
    ctx.actions.run(
        outputs = [scrambled_vmem],
        inputs = [
            ctx.file.vmem,
            ctx.executable._tool,
        ],
        arguments = [
            ctx.file.vmem.path,
            scrambled_vmem.path,
        ],
        executable = ctx.executable._tool,
    )
    return [DefaultInfo(
        files = depset(outputs),
        data_runfiles = ctx.runfiles(files = outputs),
    )]

scramble_flash_vmem = rv_rule(
    implementation = _scramble_flash_vmem_impl,
    attrs = {
        "vmem": attr.label(allow_single_file = True),
        "_tool": attr.label(
            default = "//util/design:gen-flash-img",
            executable = True,
            cfg = "exec",
        ),
    },
)

def _bin_to_spiflash_frames_impl(ctx):
    outputs = []
    frames_bin = ctx.actions.declare_file("{}.frames.bin".format(
        # Remove ".bin" from file basename.
        ctx.file.bin.basename.replace("." + ctx.file.bin.extension, ""),
    ))
    outputs.append(frames_bin)
    ctx.actions.run(
        outputs = [frames_bin],
        inputs = [
            ctx.file.bin,
            ctx.file._tool,
        ],
        arguments = [
            "--input",
            ctx.file.bin.path,
            "--dump-frames",
            frames_bin.path,
        ],
        executable = ctx.file._tool.path,
    )
    return [DefaultInfo(
        files = depset(outputs),
        data_runfiles = ctx.runfiles(files = outputs),
    )]

bin_to_spiflash_frames = rule(
    implementation = _bin_to_spiflash_frames_impl,
    cfg = opentitan_transition,
    attrs = {
        "bin": attr.label(allow_single_file = True),
        # TODO(lowRISC/opentitan:#11199): explore other options to side-step the
        # need for this transition, in order to build the spiflash tool.
        "platform": attr.string(default = "@local_config_platform//:host"),
        "_tool": attr.label(
            default = "//sw/host/spiflash",
            allow_single_file = True,
        ),
        "_allowlist_function_transition": attr.label(
            default = "@bazel_tools//tools/allowlists/function_transition_allowlist",
        ),
    },
)

def _gen_sim_dv_logs_db_impl(ctx):
    outputs = []
    for src in ctx.files.srcs:
        if src.extension != "elf":
            fail("can only generate DV logs database files from ELF files.")
        logs_db = ctx.actions.declare_file("{}.logs.txt".format(
            src.basename.replace("." + src.extension, ""),
        ))
        rodata = ctx.actions.declare_file("{}.rodata.txt".format(
            src.basename.replace("." + src.extension, ""),
        ))
        outputs.append(logs_db)
        outputs.append(rodata)

        ctx.actions.run(
            outputs = outputs,
            inputs = [src],
            arguments = [
                "--elf-file",
                src.path,
                "--rodata-sections",
                ".rodata",
                "--logs-fields-section",
                ".logs.fields",
                "--name",
                src.basename.replace("." + src.extension, ""),
                "--outdir",
                logs_db.dirname,
            ],
            executable = ctx.executable._tool,
        )
    return [DefaultInfo(
        files = depset(outputs),
        data_runfiles = ctx.runfiles(files = outputs),
    )]

gen_sim_dv_logs_db = rule(
    implementation = _gen_sim_dv_logs_db_impl,
    cfg = opentitan_transition,
    attrs = {
        "srcs": attr.label_list(allow_files = True),
        "platform": attr.string(default = OPENTITAN_PLATFORM),
        "_tool": attr.label(
            default = "//util/device_sw_utils:extract_sw_logs_db",
            cfg = "exec",
            executable = True,
        ),
        "_allowlist_function_transition": attr.label(
            default = "@bazel_tools//tools/allowlists/function_transition_allowlist",
        ),
    },
)

def opentitan_binary(
        name,
        platform = OPENTITAN_PLATFORM,
        output_bin = True,
        output_disassembly = True,
        extract_sw_logs_db = False,
        **kwargs):
    """A helper macro for generating OpenTitan binary artifacts.

    This macro is mostly a wrapper around cc_binary, but creates artifacts
    compatible with OpenTitan binaries. The actual artifacts created are an ELF
    file, a BIN file, the disassembly, and a log message database (text file)
    for the DV simulation testbench. Each of these output targets performs a
    bazel transition to the RV32I toolchain to build the target under the
    correct compiler.
    Args:
      @param name: The name of this rule.
      @param platform: The target platform for the artifacts.
      @param output_bin: Whether to emit a BIN file.
      @param output_disassembly: Whether to emit a disassembly file.
      @param extract_sw_logs_db: Whether to emit a log database for DV testbench.
      @param **kwargs: Arguments to forward to `cc_binary`.
    Emits rules:
      cc_binary             named: <name>
      optionally:
        obj_transform       named: <name>_bin
        elf_to_dissassembly named: <name>_dis
        gen_sim_dv_logs_db  named: <name>_sim_dv_logs
      filegroup             named: <name>
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

    # Generate ELF
    native.cc_binary(
        name = name,
        deps = deps,
        target_compatible_with = _targets_compatible_with[platform],
        copts = copts,
        linkopts = linkopts,
        **kwargs
    )

    preproc_name = "{}_{}".format(name, "preproc")
    targets.append(preproc_name)
    rv_preprocess(
        name = preproc_name,
        target = name,
    )

    asm_name = "{}_{}".format(name, "asm")
    targets.append(asm_name)
    rv_asm(
        name = asm_name,
        target = name,
    )

    ll_name = "{}_{}".format(name, "ll")
    targets.append(ll_name)
    rv_llvm_ir(
        name = ll_name,
        target = name,
    )

    map_name = "{}_{}".format(name, "map")
    targets.append(map_name)
    rv_relink_with_linkmap(
        name = map_name,
        target = name,
    )

    elf_name = "{}_{}".format(name, "elf")
    targets.append(":" + elf_name)
    obj_transform(
        name = elf_name,
        srcs = [name],
        format = "elf32-little",
        suffix = "elf",
        platform = platform,
    )

    # Generate Binary
    if output_bin:
        bin_name = "{}_{}".format(name, "bin")
        targets.append(":" + bin_name)
        obj_transform(
            name = bin_name,
            srcs = [name],
            platform = platform,
        )

    # Generate Disassembly
    if output_disassembly:
        dis_name = "{}_{}".format(name, "dis")
        targets.append(":" + dis_name)
        elf_to_disassembly(
            name = dis_name,
            srcs = [name],
            platform = platform,
        )

    # Generate log message database for DV sim testbench
    if extract_sw_logs_db:
        logs_db_name = "{}_{}".format(name, "logs_db")
        targets.append(":" + logs_db_name)
        gen_sim_dv_logs_db(
            name = logs_db_name,
            srcs = [elf_name],
            platform = platform,
        )

    native.filegroup(
        name = name + "_base_bins",
        srcs = targets,
    )

    return targets

def opentitan_rom_binary(
        name,
        platform = OPENTITAN_PLATFORM,
        per_device_deps = PER_DEVICE_DEPS,
        extract_sw_logs_db = True,
        **kwargs):
    """A helper macro for generating OpenTitan binary artifacts for ROM.

    This macro is mostly a wrapper around a opentitan_binary macro, which
    itself is a wrapper around cc_binary, but also creates artifacts for each
    of the keys in `per_device_deps`. The actual artifacts created are an ELF
    file, a BIN file, the disassembly, the sim_dv logs database, the
    unscrambled (ROM) VMEM file, and the scrambled (ROM) VMEM file. Each of
    these output targets performs a bazel transition to the RV32I toolchain to
    build the target under the correct compiler.
    Args:
      @param name: The name of this rule.
      @param platform: The target platform for the artifacts.
      @param per_device_deps: The deps for each of the hardware target.
      @param extract_sw_logs_db: Whether to extract SW logs database for DV sim.
      @param **kwargs: Arguments to forward to `opentitan_binary`.
    Emits rules:
      For each device in per_device_deps entry:
        cc_binary                 named: <name>_<device>
        obj_transform             named: <name>_<device>_elf
        obj_transform             named: <name>_<device>_bin
        elf_to_dissassembly       named: <name>_<device>_dis
        bin_to_rom_vmem           named: <name>_<device>_vmem
        elf_to_scrambled_rom_vmem named: <name>_<device>_scr_vmem
      For the sim_dv device:
        gen_sim_dv_logs_db        named: <name>_sim_dv_logs
      filegroup named: <name>
          with all the generated rules
    """

    deps = kwargs.pop("deps", [])
    targets = []
    for (device, dev_deps) in per_device_deps.items():
        devname = "{}_{}".format(name, device)

        # Generate ELF, Binary, Disassembly, and (maybe) sim_dv logs database
        targets.extend(opentitan_binary(
            name = devname,
            deps = deps + dev_deps,
            extract_sw_logs_db = extract_sw_logs_db and device.startswith("sim_"),
            **kwargs
        ))
        elf_name = "{}_{}".format(devname, "elf")
        bin_name = "{}_{}".format(devname, "bin")

        # Generate Un-scrambled ROM VMEM
        vmem_name = "{}_vmem".format(devname)
        targets.append(":" + vmem_name)
        bin_to_vmem(
            name = vmem_name,
            bin = bin_name,
            platform = platform,
            word_size = 32, 
        )

        # Generate Scrambled ROM VMEM
        scr_vmem_name = "{}_scr_vmem".format(devname)
        targets.append(":" + scr_vmem_name)
        elf_to_scrambled_rom_vmem(
            name = scr_vmem_name,
            srcs = [elf_name],
            platform = platform,
        )

    native.filegroup(
        name = name,
        srcs = targets,
    )

def opentitan_flash_binary(
        name,
        platform = OPENTITAN_PLATFORM,
        signing_keys = {
            "test_key_0": "//sw/device/silicon_creator/mask_rom/keys:test_private_key_0",
        },
        per_device_deps = PER_DEVICE_DEPS,
        extract_sw_logs_db = True,
        output_signed = False,
        **kwargs):
    """A helper macro for generating OpenTitan binary artifacts for flash.

    This macro is mostly a wrapper around a opentitan_binary macro, which itself
    is a wrapper around cc_binary, but also creates artifacts for each of the
    keys in `per_device_deps`, and if signing is enabled, each of the keys in
    `signing_keys`. The actual artifacts created are an ELF file, a (signed and)
    unsigned BIN file, the disassembly, the sim_dv logs database, a (signed and)
    unsigned flash VMEM file, and a (signed and) unsigned scrambled flash VMEM
    file. Some of these output targets perform a bazel transition to the RV32I
    toolchain to build the target under the correct compiler.
    Args:
      @param name: The name of this rule.
      @param platform: The target platform for the artifacts.
      @param signing_keys: The signing keys for to sign each BIN file with.
      @param per_device_deps: The deps for each of the hardware target.
      @param extract_sw_logs_db: Whether to extract SW logs database for DV sim.
      @param output_signed: Whether or not to emit signed binary/VMEM files.
      @param **kwargs: Arguments to forward to `opentitan_binary`.
    Emits rules:
      For each device in per_device_deps entry:
        cc_binary              named: <name>_<device>
        obj_transform          named: <name>_<device>_elf
        obj_transform          named: <name>_<device>_bin
        elf_to_dissassembly    named: <name>_<device>_dis
        bin_to_vmem            named: <name>_<device>_flash_vmem
        scrambled_flash_vmem   named: <name>_<device>_scr_flash_vmem
        optionally:
          sign_bin             named: <name>_<device>_bin_signed_<key_name>
          bin_to_vmem          named: <name>_<device>_flash_vmem_signed_<key_name>
          scrambled_flash_vmem named: <name>_<device>_scr_flash_vmem_signed_<key_name>
      For the sim_dv device:
        gen_sim_dv_logs_db     named: <name>_sim_dv_logs
      filegroup named: <name>
          with all the generated rules
    """

    deps = kwargs.pop("deps", [])
    targets = []
    for (device, dev_deps) in per_device_deps.items():
        devname = "{}_{}".format(name, device)

        # Generate ELF, Binary, Disassembly, and (maybe) sim_dv logs database
        targets.extend(opentitan_binary(
            name = devname,
            deps = deps + dev_deps,
            extract_sw_logs_db = extract_sw_logs_db and device.startswith("sim_"),
            **kwargs
        ))
        elf_name = "{}_{}".format(devname, "elf")
        bin_name = "{}_{}".format(devname, "bin")

        # Generate SPI flash frames binary for bootstrap in DV sim.
        if device == "sim_dv":
            frames_bin_name = "{}_frames_bin".format(devname)
            targets.append(":" + frames_bin_name)
            bin_to_spiflash_frames(
                name = frames_bin_name,
                bin = bin_name,
            )
            frames_vmem_name = "{}_frames_vmem".format(devname)
            targets.append(":" + frames_vmem_name)
            bin_to_vmem(
                name = frames_vmem_name,
                bin = frames_bin_name,
                platform = platform,
                word_size = 32,  # Bootstrap VMEM image uses 32-bit words
            )

        # Sign BIN (if required) and generate scrambled VMEM images.
        if output_signed:
            for (key_name, key) in signing_keys.items():
                # Sign the Binary.
                signed_bin_name = "{}_bin_signed_{}".format(devname, key_name)
                targets.append(":" + signed_bin_name)
                sign_bin(
                    name = signed_bin_name,
                    bin = bin_name,
                    elf = elf_name,
                    key = key,
                    key_name = key_name,
                )

                # Generate a VMEM64 from the signed binary.
                signed_vmem_name = "{}_vmem64_signed_{}".format(
                    devname,
                    key_name,
                )
                targets.append(":" + signed_vmem_name)
                bin_to_vmem(
                    name = signed_vmem_name,
                    bin = signed_bin_name,
                    platform = platform,
                    word_size = 64,  # Backdoor-load VMEM image uses 64-bit words
                )

                # Scramble signed VMEM64.
                scr_signed_vmem_name = "{}_scr_vmem64_signed_{}".format(
                    devname,
                    key_name,
                )
                targets.append(":" + scr_signed_vmem_name)
                scramble_flash_vmem(
                    name = scr_signed_vmem_name,
                    vmem = signed_vmem_name,
                    platform = platform,
                )
        else:
            # Generate a VMEM64 from the binary.
            vmem_name = "{}_vmem64".format(devname)
            targets.append(":" + vmem_name)
            bin_to_vmem(
                name = vmem_name,
                bin = bin_name,
                platform = platform,
                word_size = 64,  # Backdoor-load VMEM image uses 64-bit words
            )

            # Scramble VMEM64.
            scr_vmem_name = "{}_scr_vmem64".format(devname)
            targets.append(":" + scr_vmem_name)
            scramble_flash_vmem(
                name = scr_vmem_name,
                vmem = vmem_name,
                platform = platform,
            )

    native.filegroup(
        name = name,
        srcs = targets,
    )
