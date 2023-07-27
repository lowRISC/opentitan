# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:const.bzl", "CONST")
load("//rules:signing.bzl", "sign_bin")
load("@rules_cc//cc:action_names.bzl", "ACTION_NAMES")
load("@rules_cc//cc:find_cc_toolchain.bzl", "find_cc_toolchain")
load(
    "@lowrisc_opentitan//rules:cc_side_outputs.bzl",
    "rv_asm",
    "rv_llvm_ir",
    "rv_preprocess",
    "rv_relink_with_linkmap",
)
load(
    "@lowrisc_opentitan//rules:rv.bzl",
    "rv_rule",
    _OPENTITAN_CPU = "OPENTITAN_CPU",
    _OPENTITAN_PLATFORM = "OPENTITAN_PLATFORM",
    _opentitan_transition = "opentitan_transition",
)
load("@crt//rules:transition.bzl", "platform_target")
load("@bazel_skylib//rules:common_settings.bzl", "BuildSettingInfo")
load("@bazel_skylib//lib:structs.bzl", "structs")

"""Rules to build OpenTitan for the RISC-V target"""

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
# simulation platforms (DV and Verilator), and two FPGA platforms (CW305
# and CW310).
PER_DEVICE_DEPS = {
    "sim_verilator": ["@//sw/device/lib/arch:sim_verilator"],
    "sim_dv": ["@//sw/device/lib/arch:sim_dv"],
    "fpga_cw305": ["@//sw/device/lib/arch:fpga_cw305"],
    "fpga_cw310": ["@//sw/device/lib/arch:fpga_cw310"],
}

def create_key_(name, label, hw_lc_states):
    return struct(
        name = name,
        label = label,
        hw_lc_states = hw_lc_states,
    )

def create_test_key(name, label):
    return create_key_(name, label, [
        CONST.LCV.TEST_UNLOCKED0,
        CONST.LCV.TEST_UNLOCKED1,
        CONST.LCV.TEST_UNLOCKED2,
        CONST.LCV.TEST_UNLOCKED3,
        CONST.LCV.TEST_UNLOCKED4,
        CONST.LCV.TEST_UNLOCKED5,
        CONST.LCV.TEST_UNLOCKED6,
        CONST.LCV.TEST_UNLOCKED7,
        CONST.LCV.RMA,
    ])

def create_dev_key(name, label):
    return create_key_(name, label, [
        CONST.LCV.DEV,
    ])

def create_prod_key(name, label):
    return create_key_(name, label, [
        CONST.LCV.TEST_UNLOCKED0,
        CONST.LCV.TEST_UNLOCKED1,
        CONST.LCV.TEST_UNLOCKED2,
        CONST.LCV.TEST_UNLOCKED3,
        CONST.LCV.TEST_UNLOCKED4,
        CONST.LCV.TEST_UNLOCKED5,
        CONST.LCV.TEST_UNLOCKED6,
        CONST.LCV.TEST_UNLOCKED7,
        CONST.LCV.DEV,
        CONST.LCV.PROD,
        CONST.LCV.PROD_END,
        CONST.LCV.RMA,
    ])

def create_key_struct(rsa_key, spx_key):
    return struct(
        rsa = rsa_key,
        spx = spx_key,
    )

# Keys available in the repo
SILICON_CREATOR_KEYS = struct(
    FAKE = struct(
        RSA = struct(
            TEST = [
                create_test_key("fake_rsa_test_key_0", "@//sw/device/silicon_creator/rom/keys/fake/rsa:test_private_key_0"),
            ],
            DEV = [
                create_dev_key("fake_rsa_dev_key_0", "@//sw/device/silicon_creator/rom/keys/fake/rsa:dev_private_key_0"),
            ],
            PROD = [
                create_prod_key("fake_rsa_prod_key_0", "@//sw/device/silicon_creator/rom/keys/fake/rsa:prod_private_key_0"),
            ],
        ),
        SPX = struct(
            TEST = [
                create_test_key("fake_spx_test_key_0", "@//sw/device/silicon_creator/rom/keys/fake/spx:test_key_0_spx"),
            ],
            DEV = [
                create_dev_key("fake_spx_dev_key_0", "@//sw/device/silicon_creator/rom/keys/fake/spx:dev_key_0_spx"),
            ],
            PROD = [
                create_prod_key("fake_spx_prod_key_0", "@//sw/device/silicon_creator/rom/keys/fake/spx:prod_key_0_spx"),
            ],
        ),
    ),
    # We can't expose real private keys publicly.
    REAL = None,
    UNAUTHORIZED = struct(
        RSA = [
            create_key_("rsa_unauthorized_0", "@//sw/device/silicon_creator/rom/keys/unauthorized/rsa:unauthorized_private_key_0", []),
        ],
        SPX = [
            create_key_("spx_unauthorized_0", "@//sw/device/silicon_creator/rom/keys/unauthorized/spx:unauthorized_0_spx", []),
        ],
    ),
)

SILICON_OWNER_KEYS = struct(
    FAKE = struct(
        RSA = struct(
            TEST = [
                create_test_key("fake_rsa_rom_ext_test_key_0", "@//sw/device/silicon_creator/rom_ext/keys/fake:rom_ext_test_private_key_0"),
            ],
            DEV = [
                create_dev_key("fake_rsa_rom_ext_dev_key_0", "@//sw/device/silicon_creator/rom_ext/keys/fake:rom_ext_dev_private_key_0"),
            ],
            PROD = None,
        ),
        # We can't expose real private keys publicly.
        REAL = None,
        UNAUTHORIZED = None,
    ),
)

def flatten(l):
    return [item for ll in l for item in ll]

def key_allowed_in_lc_state(key, hw_lc_state_val):
    all_hw_lc_state_vals = structs.to_dict(CONST.LCV).values()
    if not hw_lc_state_val in all_hw_lc_state_vals:
        fail("Wrong life cycle state value: '{}', must be one of {}. Did you pass a string instead of the integer value?".format(hw_lc_state_val, all_hw_lc_state_vals))
    return hw_lc_state_val in key.hw_lc_states

def get_key_structs_for_lc_state(hw_lc_state, rsa = SILICON_CREATOR_KEYS.FAKE.RSA, spx = SILICON_CREATOR_KEYS.FAKE.SPX):
    # [(rsa_key, spx_key), ...]
    if rsa and spx:
        rsa = flatten(structs.to_dict(s = rsa).values())
        spx = flatten(structs.to_dict(s = spx).values())
    elif rsa and not spx:
        rsa = flatten(structs.to_dict(s = rsa).values())
        spx = [None] * len(rsa)
    elif not rsa and spx:
        spx = flatten(structs.to_dict(s = spx).values())
        rsa = [None] * len(spx)
    else:
        fail("No keys were provided")

    if len(rsa) != len(spx):
        fail("Lists have different lengths")
    keys = zip(rsa, spx)
    res = [
        create_key_struct(rsa, spx)
        for rsa, spx in keys
        if (rsa == None or key_allowed_in_lc_state(rsa, hw_lc_state)) and (spx == None or key_allowed_in_lc_state(spx, hw_lc_state))
    ]
    return res

def filter_key_structs_for_lc_state(key_structs, hw_lc_state):
    return [k for k in key_structs if (not k.rsa or key_allowed_in_lc_state(k.rsa, hw_lc_state)) and (not k.spx or key_allowed_in_lc_state(k.spx, hw_lc_state))]

RSA_ONLY_KEY_STRUCTS = [
    create_key_struct(SILICON_CREATOR_KEYS.FAKE.RSA.TEST[0], None),
    create_key_struct(SILICON_CREATOR_KEYS.FAKE.RSA.DEV[0], None),
    create_key_struct(SILICON_CREATOR_KEYS.FAKE.RSA.PROD[0], None),
    create_key_struct(SILICON_CREATOR_KEYS.UNAUTHORIZED.RSA[0], None),
]

RSA_SPX_KEY_STRUCTS = [
    create_key_struct(SILICON_CREATOR_KEYS.FAKE.RSA.TEST[0], SILICON_CREATOR_KEYS.FAKE.SPX.TEST[0]),
    create_key_struct(SILICON_CREATOR_KEYS.FAKE.RSA.DEV[0], SILICON_CREATOR_KEYS.FAKE.SPX.DEV[0]),
    create_key_struct(SILICON_CREATOR_KEYS.FAKE.RSA.PROD[0], SILICON_CREATOR_KEYS.FAKE.SPX.PROD[0]),
    create_key_struct(SILICON_CREATOR_KEYS.UNAUTHORIZED.RSA[0], SILICON_CREATOR_KEYS.UNAUTHORIZED.SPX[0]),
]

RSA_ONLY_ROM_EXT_KEY_STRUCTS = [
    create_key_struct(SILICON_OWNER_KEYS.FAKE.RSA.TEST[0], None),
    create_key_struct(SILICON_OWNER_KEYS.FAKE.RSA.DEV[0], None),
]

def _obj_transform_impl(ctx):
    cc_toolchain = find_cc_toolchain(ctx).cc
    outputs = []
    for src in ctx.files.srcs:
        binary = ctx.actions.declare_file(
            "{}.{}".format(
                src.basename.replace("." + src.extension, ""),
                ctx.attr.suffix,
            ),
        )
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

# A provider for device-specific archive files that hold binaries of SRAM programs.
ArchiveInfo = provider(fields = ["archive_infos"])

def _bin_to_archive_impl(ctx):
    cc_infos = []
    cc_toolchain = find_cc_toolchain(ctx).cc
    cc_info_dict = {}
    num_devices = len(ctx.attr.devices)
    num_binaries = len(ctx.attr.binaries)
    if num_devices != num_binaries:
        fail("Number of devices", num_devices, "must be equal to number of binaries", num_binaries)
    for (device, binary_target) in zip(ctx.attr.devices, ctx.attr.binaries):
        devname = "{}_{}".format(ctx.attr.name, device)
        binary_file = binary_target.files.to_list()[0]
        object_file = ctx.actions.declare_file("{}.o".format(devname))
        renamed_object_file = ctx.actions.declare_file("{}.renamed.o".format(devname))
        archive_file = ctx.actions.declare_file("{}.a".format(devname))

        # Create a CcInfo to be able to use this rule as a dependency in other rules.
        # See https://bazel.build/docs/integrating-with-rules-cc.
        feature_configuration = cc_common.configure_features(
            ctx = ctx,
            cc_toolchain = cc_toolchain,
            requested_features = ctx.features,
            unsupported_features = ctx.disabled_features,
        )
        action_name = ACTION_NAMES.cpp_link_executable
        c_linker_path = cc_common.get_tool_for_action(
            feature_configuration = feature_configuration,
            action_name = action_name,
        )
        c_link_variables = cc_common.create_link_variables(
            feature_configuration = feature_configuration,
            cc_toolchain = cc_toolchain,
            output_file = object_file.path,
        )
        command_line = cc_common.get_memory_inefficient_command_line(
            feature_configuration = feature_configuration,
            action_name = action_name,
            variables = c_link_variables,
        )
        env = cc_common.get_environment_variables(
            feature_configuration = feature_configuration,
            action_name = action_name,
            variables = c_link_variables,
        )
        linker_path = cc_common.get_tool_for_action(
            feature_configuration = feature_configuration,
            action_name = action_name,
        )

        # Create an object file that contains the binary.
        ctx.actions.run(
            executable = cc_toolchain.ld_executable,
            arguments = [
                "-r",
                "-b",
                "binary",
                "-o",
                object_file.path,
                binary_file.path,
            ],
            use_default_shell_env = False,
            env = env,
            inputs = depset(
                direct = [binary_file],
                transitive = [cc_toolchain.all_files],
            ),
            outputs = [object_file],
            mnemonic = "CppLink",
        )

        # Rename symbols to make them more manageable.
        sym_prefix = "_binary_" + binary_file.path.replace(".", "_").replace("/", "_").replace("-", "_")
        suffixes = ["start", "end", "size"]
        rename_args = []
        for suffix in suffixes:
            old_name = "{}_{}".format(sym_prefix, suffix)
            new_name = "_{}_{}".format(ctx.attr.archive_symbol_prefix, suffix)
            rename_args.extend(["--redefine-sym", "{}={}".format(old_name, new_name)])
        rename_args.extend(["--rename-section", ".data=.data.sram_program"])
        rename_args.extend([object_file.path, renamed_object_file.path])
        ctx.actions.run(
            executable = cc_toolchain.objcopy_executable,
            arguments = rename_args,
            use_default_shell_env = False,
            env = env,
            inputs = depset(
                direct = [object_file],
                transitive = [cc_toolchain.all_files],
            ),
            outputs = [renamed_object_file],
            mnemonic = "RenameSymbols",
        )

        # Create an archive that contains the object file.
        ctx.actions.run(
            executable = cc_toolchain.ar_executable,
            arguments = [
                "r",
                archive_file.path,
                renamed_object_file.path,
            ],
            use_default_shell_env = False,
            env = env,
            inputs = depset(
                direct = [renamed_object_file],
                transitive = [cc_toolchain.all_files],
            ),
            outputs = [archive_file],
            mnemonic = "Archive",
        )

        cc_info_dict[device] = CcInfo(
            compilation_context = cc_common.create_compilation_context(
                headers = depset(direct = ctx.attr.hdrs[0].files.to_list()),
            ),
            linking_context = cc_common.create_linking_context(
                linker_inputs = depset([cc_common.create_linker_input(
                    owner = ctx.label,
                    libraries = depset([cc_common.create_library_to_link(
                        actions = ctx.actions,
                        feature_configuration = feature_configuration,
                        cc_toolchain = cc_toolchain,
                        static_library = archive_file,
                    )]),
                )]),
            ),
        )

    return ArchiveInfo(archive_infos = cc_info_dict)

bin_to_archive = rv_rule(
    implementation = _bin_to_archive_impl,
    attrs = {
        "binaries": attr.label_list(allow_files = True),
        "devices": attr.string_list(),
        "hdrs": attr.label_list(allow_files = True),
        "archive_symbol_prefix": attr.string(),
        "_cc_toolchain": attr.label(default = Label("@bazel_tools//tools/cpp:current_cc_toolchain")),
    },
    fragments = ["cpp"],
    toolchains = ["@rules_cc//cc:toolchain_type"],
)

def _elf_to_disassembly_impl(ctx):
    cc_toolchain = find_cc_toolchain(ctx).cc
    outputs = []
    for src in ctx.files.srcs:
        disassembly = ctx.actions.declare_file(
            "{}.dis".format(
                src.basename.replace("." + src.extension, ""),
            ),
        )
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
            execution_requirements = {
                "no-sandbox": "1",
            },
            command = "$1 -wx --disassemble --headers --line-numbers --disassemble-zeroes --source --visualize-jumps $2 | $3 > $4",
        )
        return [DefaultInfo(files = depset(outputs), data_runfiles = ctx.runfiles(files = outputs))]

elf_to_disassembly = rv_rule(
    implementation = _elf_to_disassembly_impl,
    attrs = {
        "srcs": attr.label_list(allow_files = True),
        "platform": attr.string(default = OPENTITAN_PLATFORM),
        "_cleanup_script": attr.label(
            allow_single_file = True,
            default = Label("@//rules/scripts:expand_tabs.sh"),
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
            "{}.39.scr.vmem".format(
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
        "data": attr.label_list(allow_files = True),
        "_scramble_tool": attr.label(
            default = "@//hw/ip/rom_ctrl/util:scramble_image",
            executable = True,
            cfg = "exec",
        ),
        "_config": attr.label(
            default = "@//hw/top_earlgrey/data:autogen/top_earlgrey.gen.hjson",
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
        use_default_shell_env = True,
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
    # Declare outputs.
    outputs = []
    scrambled_vmem = ctx.actions.declare_file("{}.scr.vmem".format(
        # Remove ".vmem" from file basename.
        ctx.file.vmem.basename.replace("." + ctx.file.vmem.extension, ""),
    ))
    outputs.append(scrambled_vmem)

    # Build arguments / inputs to `gen-flash-img.py` script.
    arguments = [
        "--in-flash-vmem",
        ctx.file.vmem.path,
        "--out-flash-vmem",
        scrambled_vmem.path,
    ]
    inputs = [
        ctx.file.vmem,
        ctx.executable._tool,
    ]
    if ctx.file.otp:
        arguments.extend([
            "--in-otp-vmem",
            ctx.file.otp.path,
            "--in-otp-mmap",
            ctx.file.otp_mmap.path,
        ])
        inputs.extend([
            ctx.file.otp,
            ctx.file.otp_mmap,
        ])
        arguments.extend([
            "--otp-seed",
            str(ctx.attr.otp_seed[BuildSettingInfo].value),
        ])
        if ctx.attr.otp_data_perm:
            arguments.extend([
                "--otp-data-perm",
                ctx.attr.otp_data_perm[BuildSettingInfo].value,
            ])

    # Run the action script.
    ctx.actions.run(
        outputs = outputs,
        inputs = inputs,
        arguments = arguments,
        executable = ctx.executable._tool,
    )
    return [DefaultInfo(
        files = depset(outputs),
        data_runfiles = ctx.runfiles(files = outputs),
    )]

scramble_flash_vmem = rv_rule(
    implementation = _scramble_flash_vmem_impl,
    attrs = {
        "otp": attr.label(allow_single_file = True),
        "otp_mmap": attr.label(
            allow_single_file = True,
            default = "//hw/ip/otp_ctrl/data:otp_ctrl_mmap.hjson",
            doc = "OTP memory map configuration HJSON file.",
        ),
        "otp_seed": attr.label(
            default = "//hw/ip/otp_ctrl/data:otp_seed",
            doc = "Configuration override seed used to randomize OTP netlist constants.",
        ),
        "vmem": attr.label(allow_single_file = True),
        "otp_data_perm": attr.label(
            default = "//hw/ip/otp_ctrl/data:data_perm",
            doc = "Option to indicate OTP VMEM file bit layout.",
        ),
        "_tool": attr.label(
            default = "@//util/design:gen-flash-img",
            executable = True,
            cfg = "exec",
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
            default = "@//util/device_sw_utils:extract_sw_logs_db",
            cfg = "exec",
            executable = True,
        ),
        "_allowlist_function_transition": attr.label(
            default = "@bazel_tools//tools/allowlists/function_transition_allowlist",
        ),
    },
)

def _assemble_flash_image_impl(ctx):
    output = ctx.actions.declare_file(ctx.attr.output)
    outputs = [output]
    inputs = []
    arguments = [
        "--rcfile=",
        "image",
        "assemble",
        "--mirror",
        "false",
        "--output",
        output.path,
    ]
    if ctx.attr.image_size:
        arguments.append("--size={}".format(ctx.attr.image_size))
    for binary, offset in ctx.attr.binaries.items():
        inputs.extend(binary.files.to_list())
        arguments.append("{}@{}".format(binary.files.to_list()[0].path, offset))
    ctx.actions.run(
        outputs = outputs,
        inputs = inputs,
        arguments = arguments,
        executable = ctx.executable._opentitantool,
    )
    return [DefaultInfo(
        files = depset(outputs),
        data_runfiles = ctx.runfiles(files = outputs),
    )]

assemble_flash_image = rv_rule(
    implementation = _assemble_flash_image_impl,
    attrs = {
        "image_size": attr.int(default = 0, doc = "Size of the assembled image"),
        "output": attr.string(),
        "binaries": attr.label_keyed_string_dict(allow_empty = False),
        "_opentitantool": attr.label(
            default = "//sw/host/opentitantool:opentitantool",
            allow_single_file = True,
            executable = True,
            cfg = "exec",
        ),
    },
)

def opentitan_binary(
        name,
        platform = OPENTITAN_PLATFORM,
        extract_sw_logs_db = False,
        testonly = False,
        **kwargs):
    """A helper macro for generating OpenTitan binary artifacts.

    This macro is mostly a wrapper around cc_binary, but creates artifacts
    compatible with OpenTitan binaries. The actual artifacts created are outputs
    of the rules listed below.
    Args:
      @param name: The name of this rule.
      @param platform: The target platform for the artifacts.
      @param extract_sw_logs_db: Whether to emit a log database for DV testbench.
      @param **kwargs: Arguments to forward to `cc_binary`.
    Emits rules:
      cc_binary             named: <name>.elf
      cc_binary+transition  named: <name>_elf_transition
      rv_preprocess         named: <name>_preproc
      rv_asm                named: <name>_asm
      rv_llvm_ir            named: <name>_ll
      rv_relink_with_map    named: <name>_map
      obj_transform         named: <name>_bin
      elf_to_dissassembly   named: <name>_dis
      Optionally:
        gen_sim_dv_logs_db  named: <name>_logs_db
    Returns:
      List of targets generated by all of the above rules.
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
    side_targets = []

    native_binary_name = "{}.elf".format(name)
    native.cc_binary(
        name = native_binary_name,
        deps = deps,
        target_compatible_with = _targets_compatible_with[platform],
        copts = copts,
        linkopts = linkopts,
        testonly = testonly,
        **kwargs
    )
    elf_transition_binary_name = "{}_elf_transition".format(name)
    targets.append(":" + elf_transition_binary_name)
    platform_target(
        name = elf_transition_binary_name,
        platform = platform,
        target = native_binary_name,
        testonly = testonly,
    )

    preproc_name = "{}_{}".format(name, "preproc")
    side_targets.append(preproc_name)
    rv_preprocess(
        name = preproc_name,
        target = native_binary_name,
        testonly = testonly,
    )

    asm_name = "{}_{}".format(name, "asm")
    side_targets.append(asm_name)
    rv_asm(
        name = asm_name,
        target = native_binary_name,
        testonly = testonly,
    )

    ll_name = "{}_{}".format(name, "ll")
    side_targets.append(ll_name)
    rv_llvm_ir(
        name = ll_name,
        target = native_binary_name,
        testonly = testonly,
    )

    map_name = "{}_{}".format(name, "map")
    side_targets.append(map_name)
    rv_relink_with_linkmap(
        name = map_name,
        target = native_binary_name,
        testonly = testonly,
    )

    bin_name = "{}_{}".format(name, "bin")
    targets.append(":" + bin_name)
    obj_transform(
        name = bin_name,
        srcs = [native_binary_name],
        platform = platform,
        testonly = testonly,
    )

    dis_name = "{}_{}".format(name, "dis")
    targets.append(":" + dis_name)
    elf_to_disassembly(
        name = dis_name,
        srcs = [native_binary_name],
        platform = platform,
        testonly = testonly,
    )

    # Generate log message database for DV sim testbench
    if extract_sw_logs_db:
        logs_db_name = "{}_{}".format(name, "logs_db")
        targets.append(":" + logs_db_name)
        gen_sim_dv_logs_db(
            name = logs_db_name,
            srcs = [native_binary_name],
            platform = platform,
            testonly = testonly,
        )

    # Create a filegroup with just the sides targets.
    native.filegroup(
        name = name + "_side_targets",
        srcs = side_targets,
        testonly = testonly,
    )

    return targets

def opentitan_rom_binary(
        name,
        devices = PER_DEVICE_DEPS.keys(),
        platform = OPENTITAN_PLATFORM,
        testonly = False,
        **kwargs):
    """A helper macro for generating OpenTitan binary artifacts for ROM.

    This macro is mostly a wrapper around the `opentitan_binary` macro, but also
    creates artifacts for each of the keys in `PER_DEVICE_DEPS`. The actual
    artifacts created are outputs of the rules emitted by the `opentitan_binary`
    macro and those listed below.
    Args:
      @param name: The name of this rule.
      @param devices: List of devices to build the target for.
      @param platform: The target platform for the artifacts.
      @param **kwargs: Arguments to forward to `opentitan_binary`.
    Emits rules:
      For each device in per_device_deps entry:
        rules emitted by `opentitan_binary` named: see `opentitan_binary` macro
        bin_to_rom_vmem                     named: <name>_<device>_vmem
        elf_to_scrambled_rom_vmem           named: <name>_<device>_scr_vmem
        filegroup                           named: <name>_<device>
          Containing all targets for a single device for the above generated rules.
        filegroup                           named: <name>
          Containing all targets across all devices for the above generated rules.
    """
    deps = kwargs.pop("deps", [])
    all_targets = []
    for device in devices:
        if device not in PER_DEVICE_DEPS:
            fail("invalid device; device must be in {}".format(PER_DEVICE_DEPS.keys()))
        dev_deps = PER_DEVICE_DEPS[device]
        devname = "{}_{}".format(name, device)
        dev_targets = []

        # Generate ELF, Binary, Disassembly, and (maybe) sim_dv logs database
        dev_targets.extend(opentitan_binary(
            name = devname,
            deps = deps + dev_deps,
            extract_sw_logs_db = device == "sim_dv",
            testonly = testonly,
            **kwargs
        ))

        # We need to generate VMEM files even for FPGA devices, because we use
        # them for bitstream splicing.
        elf_name = "{}.{}".format(devname, "elf")
        bin_name = "{}_{}".format(devname, "bin")

        # Generate Un-scrambled ROM VMEM
        vmem_name = "{}_vmem".format(devname)
        dev_targets.append(":" + vmem_name)
        bin_to_vmem(
            name = vmem_name,
            bin = bin_name,
            platform = platform,
            testonly = testonly,
            word_size = 32,
        )

        # Generate Scrambled ROM VMEM
        scr_vmem_name = "{}_scr_vmem".format(devname)
        dev_targets.append(":" + scr_vmem_name)
        elf_to_scrambled_rom_vmem(
            name = scr_vmem_name,
            srcs = [elf_name],
            platform = platform,
            testonly = testonly,
        )

        # Create a filegroup with just the current device's targets.
        native.filegroup(
            name = devname,
            srcs = dev_targets,
            testonly = testonly,
        )
        all_targets.extend(dev_targets)

    # Create a filegroup with just all targets from all devices.
    native.filegroup(
        name = name,
        srcs = all_targets,
        testonly = testonly,
    )

def _pick_correct_archive_for_device(ctx):
    cc_infos = []
    for dep in ctx.attr.deps:
        if CcInfo in dep:
            cc_info = dep[CcInfo]
        elif ArchiveInfo in dep:
            cc_info = dep[ArchiveInfo].archive_infos[ctx.attr.device]
        else:
            fail("Expected either a CcInfo or an ArchiveInfo")
        cc_infos.append(cc_info)
    return [cc_common.merge_cc_infos(cc_infos = cc_infos)]

pick_correct_archive_for_device = rv_rule(
    implementation = _pick_correct_archive_for_device,
    attrs = {
        "deps": attr.label_list(allow_files = True),
        "device": attr.string(),
    },
    fragments = ["cpp"],
    toolchains = ["@rules_cc//cc:toolchain_type"],
)

def opentitan_multislot_flash_binary(
        name,
        srcs,
        image_size = 0,
        devices = PER_DEVICE_DEPS.keys(),
        platform = OPENTITAN_PLATFORM,
        testonly = False):
    """A helper macro for generating multislot OpenTitan binary flash images.

    This macro is mostly a wrapper around the `assemble_flash_image` rule, that
    invokes `opentitantool` to stitch together multiple `opentitan_flash_binary`
    images to create a single image for bootstrapping. Since bootstrap erases
    the flash for programming this is the only way to load multiple
    (A/B/Virtual) slots and (silicon creator, ROM_EXT, and owner, BL0) stages at
    the same time.
    Args:
      @param name: The name of this rule.
      @param srcs: A dictionary of `opentitan_flash_binary` targets (to stitch
                   together) as keys, and key/offset configurations as values.
      @param image_size: The final flash image_size to pass to `opentitantool`
                         (optional).
      @param devices: List of devices to build the target for.
      @param platform: The target platform for the artifacts.
    Emits rules:
      For each device in per_device_deps entry:
        rules emitted by `opentitan_binary` named: see `opentitan_binary` macro
        assemble_flash_image named: <name>_<device>_bin_signed
        bin_to_vmem          named: <name>_<device>_vmem64_signed
        scrambled_flash_vmem named: <name>_<device>_scr_vmem64_signed
        filegroup            named: <name>_<device>
          Containing all targets for a single device for the above generated rules.
        filegroup            named: <name>
          Containing all targets across all devices for the above generated rules.
    """
    all_targets = []
    for device in devices:
        if device not in PER_DEVICE_DEPS:
            fail("invalid device; device must be in {}".format(PER_DEVICE_DEPS.keys()))
        devname = "{}_{}".format(name, device)
        dev_targets = []
        signed_dev_binaries = {}
        for src, configs in srcs.items():
            if "key" not in configs:
                fail("Missing signing key for binary: {}".format(src))
            if "offset" not in configs:
                fail("Missing offset for binary: {}".format(src))
            signed_dev_binary = "{}_{}_bin_signed_{}".format(
                src,
                device,
                configs["key"] if type(configs["key"]) == "string" else configs["key"].rsa.name,
                testonly = testonly,
            )
            signed_dev_binaries[signed_dev_binary] = configs["offset"]

        # Assemble the signed binaries into a single binary.
        signed_bin_name = "{}_bin_signed".format(devname)
        dev_targets.append(":" + signed_bin_name)
        assemble_flash_image(
            name = signed_bin_name,
            output = "{}.signed.bin".format(devname),
            image_size = image_size,
            binaries = signed_dev_binaries,
            testonly = testonly,
        )

        # We only need to generate VMEM files for sim devices.
        if device in ["sim_dv", "sim_verilator"]:
            # Generate a VMEM64 from the binary.
            signed_vmem_name = "{}_vmem64_signed".format(devname)
            dev_targets.append(":" + signed_vmem_name)
            bin_to_vmem(
                name = signed_vmem_name,
                bin = signed_bin_name,
                platform = platform,
                testonly = testonly,
                word_size = 64,  # Backdoor-load VMEM image uses 64-bit words
            )

            # Scramble signed VMEM64.
            scr_signed_vmem_name = "{}_scr_vmem64_signed".format(devname)
            dev_targets.append(":" + scr_signed_vmem_name)
            scramble_flash_vmem(
                name = scr_signed_vmem_name,
                vmem = signed_vmem_name,
                platform = platform,
                testonly = testonly,
            )

        # Create a filegroup with just the current device's targets.
        native.filegroup(
            name = devname,
            srcs = dev_targets,
            testonly = testonly,
        )
        dev_targets.extend(dev_targets)

    # Create a filegroup with all assembled flash images.
    native.filegroup(
        name = name,
        srcs = all_targets,
        testonly = testonly,
    )

def opentitan_flash_binary(
        name,
        devices = PER_DEVICE_DEPS.keys(),
        platform = OPENTITAN_PLATFORM,
        signing_key_structs = RSA_ONLY_KEY_STRUCTS + RSA_ONLY_ROM_EXT_KEY_STRUCTS,
        signed = True,
        sim_otp = None,
        testonly = False,
        manifest = "//sw/device/silicon_creator/rom_ext:manifest_standard",
        **kwargs):
    """A helper macro for generating OpenTitan binary artifacts for flash.

    This macro is mostly a wrapper around the `opentitan_binary` macro, but also
    creates artifacts for each of the keys in `PER_DEVICE_DEPS`, and if signing
    is enabled, each of the keys in `signing_key_structs`. The actual artifacts created
    artifacts created are outputs of the rules emitted by the `opentitan_binary`
    macro and those listed below.
    Args:
      @param name: The name of this rule.
      @param devices: List of devices to build the target for.
      @param platform: The target platform for the artifacts.
      @param signing_key_structs: The signing keys to sign each BIN file with.
      @param signed: Whether or not to emit signed binary/VMEM files.
      @param sim_otp: OTP image that contains flash scrambling keys / enablement flag
                      (only relevant for VMEM files built for sim targets).
      @param manifest: Partially populated manifest to set boot stage/slot configs.
      @param **kwargs: Arguments to forward to `opentitan_binary`.
    Emits rules:
      For each device in per_device_deps entry:
        rules emitted by `opentitan_binary` named: see `opentitan_binary` macro
        bin_to_vmem                         named: <name>_<device>_vmem64
        scrambled_flash_vmem                named: <name>_<device>_scr_vmem64
        Optionally:
          sign_bin             named: <name>_<device>_bin_signed_<key_name>
          bin_to_vmem          named: <name>_<device>_vmem64_signed_<key_name>
          scrambled_flash_vmem named: <name>_<device>_scr_vmem64_signed_<key_name>
        filegroup              named: <name>_<device>
          Containing all targets for a single device for the above generated rules.
        filegroup              named: <name>
          Containing all targets across all devices for the above generated rules.
    """
    deps = kwargs.pop("deps", [])
    all_targets = []
    binaries = []
    for device in devices:
        if device not in PER_DEVICE_DEPS:
            fail("invalid device; device must be in {}".format(PER_DEVICE_DEPS.keys()))
        dev_deps = PER_DEVICE_DEPS[device]
        devname = "{}_{}".format(name, device)
        dev_targets = []

        depname = "{}_deps".format(devname)
        pick_correct_archive_for_device(
            name = depname,
            deps = deps + dev_deps,
            device = device,
            testonly = testonly,
        )

        # Generate ELF, Binary, Disassembly, and (maybe) sim_dv logs database
        dev_targets.extend(opentitan_binary(
            name = devname,
            deps = [depname],
            extract_sw_logs_db = device == "sim_dv",
            testonly = testonly,
            **kwargs
        ))
        bin_name = "{}_{}".format(devname, "bin")
        binaries.append(":" + bin_name)

        # Sign BIN (if required) and generate scrambled VMEM images.
        if signed:
            if manifest == None:
                fail("A 'manifest' must be provided in order to sign flash images.")
            for key_struct in signing_key_structs:
                if key_struct.spx:
                    # Sign the binary using RSA and SPX+.
                    key_name = "{}_{}".format(key_struct.rsa.name, key_struct.spx.name)
                    signed_bin_name = "{}_bin_signed_{}".format(devname, key_name)
                    dev_targets.append(":" + signed_bin_name)
                    sign_bin(
                        name = signed_bin_name,
                        bin = bin_name,
                        rsa_key = {key_struct.rsa.label: key_struct.rsa.name},
                        spx_key = {key_struct.spx.label: key_struct.spx.name},
                        manifest = manifest,
                        testonly = testonly,
                    )
                else:
                    # Sign the binary using RSA only.
                    key_name = "{}".format(key_struct.rsa.name)
                    signed_bin_name = "{}_bin_signed_{}".format(devname, key_name)
                    dev_targets.append(":" + signed_bin_name)
                    sign_bin(
                        name = signed_bin_name,
                        bin = bin_name,
                        rsa_key = {key_struct.rsa.label: key_struct.rsa.name},
                        manifest = manifest,
                        testonly = testonly,
                    )

                # We only need to generate VMEM files for sim devices.
                if device in ["sim_dv", "sim_verilator"]:
                    # Generate a VMEM64 from the signed binary.
                    signed_vmem_name = "{}_vmem64_signed_{}".format(
                        devname,
                        key_name,
                    )
                    dev_targets.append(":" + signed_vmem_name)
                    bin_to_vmem(
                        name = signed_vmem_name,
                        bin = signed_bin_name,
                        platform = platform,
                        testonly = testonly,
                        word_size = 64,  # Backdoor-load VMEM image uses 64-bit words
                    )

                    # Scramble / compute ECC for signed VMEM64.
                    scr_signed_vmem_name = "{}_scr_vmem64_signed_{}".format(
                        devname,
                        key_name,
                    )
                    dev_targets.append(":" + scr_signed_vmem_name)
                    scramble_flash_vmem(
                        name = scr_signed_vmem_name,
                        otp = sim_otp,
                        vmem = signed_vmem_name,
                        platform = platform,
                        testonly = testonly,
                    )

        # We only need to generate VMEM files for sim devices.
        if device in ["sim_dv", "sim_verilator"]:
            # Generate a VMEM64 from the binary.
            vmem_name = "{}_vmem64".format(devname)
            dev_targets.append(":" + vmem_name)
            bin_to_vmem(
                name = vmem_name,
                bin = bin_name,
                platform = platform,
                testonly = testonly,
                word_size = 64,  # Backdoor-load VMEM image uses 64-bit words
            )

            # Scramble / compute ECC for VMEM64.
            scr_vmem_name = "{}_scr_vmem64".format(devname)
            dev_targets.append(":" + scr_vmem_name)
            scramble_flash_vmem(
                name = scr_vmem_name,
                otp = sim_otp,
                vmem = vmem_name,
                platform = platform,
                testonly = testonly,
            )

        # Create a filegroup with just the current device's targets.
        native.filegroup(
            name = devname,
            srcs = dev_targets,
            testonly = testonly,
        )
        all_targets.extend(dev_targets)

    # Create a filegroup with all targets from all devices.
    native.filegroup(
        name = name,
        srcs = all_targets,
        testonly = testonly,
    )

    # Create a filegroup with all binary targets.
    native.filegroup(
        name = name + "_bin",
        srcs = binaries,
        testonly = testonly,
    )

def opentitan_ram_binary(
        name,
        archive_symbol_prefix,
        devices = PER_DEVICE_DEPS.keys(),
        platform = OPENTITAN_PLATFORM,
        testonly = False,
        **kwargs):
    """A helper macro for generating OpenTitan binary artifacts for RAM.

    This macro is mostly a wrapper around the `opentitan_binary` macro, but also
    creates artifacts for each of the keys in `PER_DEVICE_DEPS`. The actual
    artifacts created are outputs of the rules emitted by the `opentitan_binary`
    macro and those listed below.
    Args:
      @param name: The name of this rule.
      @param archive_symbol_prefix: Prefix used to rename symbols in the binary.
      @param devices: List of devices to build the target for.
      @param platform: The target platform for the artifacts.
      @param **kwargs: Arguments to forward to `opentitan_binary`.
    Emits rules:
      For each device in per_device_deps entry:
        rules emitted by `opentitan_binary` named: see `opentitan_binary` macro
      bin_to_archive            named: <name>
      bin_to_vmem               named: <name>_<device>_vmem
    """
    deps = kwargs.pop("deps", [])
    hdrs = kwargs.pop("hdrs", [])
    binaries = []
    for device in devices:
        if device not in PER_DEVICE_DEPS:
            fail("invalid device; device must be in {}".format(PER_DEVICE_DEPS.keys()))
        dev_deps = PER_DEVICE_DEPS[device]
        devname = "{}_{}".format(name, device)
        dev_targets = []

        # Generate the binary.
        dev_targets.extend(opentitan_binary(
            name = devname,
            deps = deps + dev_deps,
            extract_sw_logs_db = device == "sim_dv",
            testonly = testonly,
            **kwargs
        ))
        bin_name = "{}_{}".format(devname, "bin")
        binaries.append(":" + bin_name)

        # Generate Un-scrambled RAM VMEM (for testing SRAM injection in DV)
        vmem_name = "{}_vmem".format(devname)
        dev_targets.append(":" + vmem_name)
        bin_to_vmem(
            name = vmem_name,
            bin = bin_name,
            platform = platform,
            testonly = testonly,
            word_size = 32,
        )

        # Create a filegroup with just the current device's targets.
        native.filegroup(
            name = devname,
            srcs = dev_targets,
            testonly = testonly,
        )

    # Generate the archive file.
    bin_to_archive(
        name = name,
        hdrs = hdrs,
        binaries = binaries,
        devices = PER_DEVICE_DEPS.keys(),
        archive_symbol_prefix = archive_symbol_prefix,
        testonly = testonly,
    )
