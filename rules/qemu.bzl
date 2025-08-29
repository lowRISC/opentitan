# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_cc//cc:find_cc_toolchain.bzl", "find_cc_toolchain")
load(
    "@rules_cc//cc:action_names.bzl",
    "CPP_LINK_EXECUTABLE_ACTION_NAME",
    "C_COMPILE_ACTION_NAME",
)
load("@bazel_skylib//rules/directory:providers.bzl", "DirectoryInfo")

def _qemu_build(ctx):
    """Build QEMU from source.

    QEMU has an unusual build flow which is roughly:

    1. Run a `configure` script (custom, not from autotools) to generate
       a Meson configuration.
    2. Run Meson to generate Ninja files.
    3. Convert the Ninja files to Makefiles.
    4. Compile code with Make.

    They have been slowly moving options from `configure` into Meson and
    making the build with just Ninja instead of Make. The project is now
    in a state where we can mostly skip the `configure` and `make` steps
    and run Meson and Ninja directly after generating a config file.

    This rule takes Meson and Ninja from `rules_foreign_cc`, but we cannot
    use their rules directly to build QEMU because of the configuration
    step.

    We need a Rust toolchain for the OTBN simulator and new Rust bindings.
    """

    # QEMU's Meson project reads this config file.
    config_host = ctx.actions.declare_file("config-host.mak")
    ctx.actions.write(
        output = config_host,
        content = "TARGET_DIRS=riscv32-softmmu\nGENISOIMAGE=",
    )

    # Take Meson and Ninja from `rules_foreign_cc`, plus a Rust and C compiler.
    meson_toolchain = ctx.toolchains[Label("@rules_foreign_cc//toolchains:meson_toolchain")]
    ninja_toolchain = ctx.toolchains[Label("@rules_foreign_cc//toolchains:ninja_toolchain")]
    rust_toolchain = ctx.toolchains[Label("@rules_rust//rust:toolchain_type")]
    cc_toolchain = find_cc_toolchain(ctx)

    # Files needed by Meson and Ninja to execute.
    meson_runfiles = meson_toolchain.data.target[DefaultInfo].files_to_run
    ninja_runfiles = ninja_toolchain.data.target[DefaultInfo].files_to_run

    meson_options = " ".join([
        "-Dauto_features=disabled",
        "-Dtrace_backends=log",
        "-Dtools=disabled",
    ])

    qemu_system_riscv32 = ctx.actions.declare_file("qemu-system-riscv32")

    ctx.actions.run_shell(
        command = " && ".join([
            # Move the config file to a build directory.
            "mkdir build",
            "cp {config} build",
            # Meson will change directories so we need absolute paths.
            'export CC="$(realpath {cc})"',
            'export RUSTC="$(realpath {rustc})"',
            'export NINJA="$(realpath {ninja})"',
            # Run both Meson and Ninja - we have to do this in one action because
            # Meson leaves `build` with dangling symlinks which Bazel doesn't like.
            "{meson} setup build {qemu_src} {meson_options}",
            "{ninja} -C build",
            # Extract the final binary.
            "cp build/qemu-system-riscv32 {qemu_system_riscv32}",
        ]).format(
            cc = cc_toolchain.compiler_executable,
            rustc = rust_toolchain.rustc.path,
            config = config_host.path,
            meson = meson_toolchain.data.path,
            meson_options = meson_options,
            ninja = ninja_toolchain.data.path,
            qemu_src = ctx.attr.qemu_src[DirectoryInfo].path,
            qemu_system_riscv32 = qemu_system_riscv32.path,
        ),
        inputs = ctx.attr.qemu_src.files.to_list() + [config_host],
        tools = rust_toolchain.all_files.to_list() +
                cc_toolchain.all_files.to_list() +
                [meson_runfiles, ninja_runfiles],
        use_default_shell_env = True,
        outputs = [qemu_system_riscv32],
        mnemonic = "QEMU",
        progress_message = "Building QEMU for %{label}",
    )

    return [
        DefaultInfo(
            files = depset([qemu_system_riscv32]),
            executable = qemu_system_riscv32,
        ),
    ]

qemu_build = rule(
    doc = "Build an RV32 QEMU system from source",
    attrs = {
        "qemu_src": attr.label(
            allow_files = True,
            providers = [DirectoryInfo],
            mandatory = True,
            doc = "Directory containing QEMU sources. See `directory` from `@bazel_skylib`",
        ),
    },
    implementation = _qemu_build,
    toolchains = [
        "@rules_foreign_cc//toolchains:meson_toolchain",
        "@rules_foreign_cc//toolchains:ninja_toolchain",
        "@rules_cc//cc:toolchain_type",
        "@rules_rust//rust:toolchain_type",
    ],
    executable = True,
)
