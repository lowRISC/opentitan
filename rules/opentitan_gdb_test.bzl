# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@lowrisc_opentitan//rules:rv.bzl", "rv_rule")

def _opentitan_gdb_fpga_cw310_test(ctx):
    test_script = '''#!/usr/bin/env bash
        set -e

        # Do not mask failures in the left-hand side of pipelines.
        set -o pipefail

        COLOR_RED='\\x1b[0;31m'
        COLOR_GREEN='\\x1b[0;32m'
        COLOR_PURPLE='\\x1b[0;35m'

        function prefix_lines() {{
            LABEL="$1"
            COLOR="$2"
            COLOR_RESET='\\x1b[m'
            sed -Eu "s/(.*)/$COLOR[$LABEL]$COLOR_RESET \\1/"
        }}

        set -x

        ./opentitantool fpga load-bitstream --rom-kind=TestRom rom.bit

        (openocd -f /usr/share/openocd/scripts/interface/ftdi/olimex-arm-usb-tiny-h.cfg \\
            -c "adapter speed 500; transport select jtag; reset_config trst_and_srst" \\
            -f {openocd_earlgrey_config} \\
            |& prefix_lines OPENOCD "$COLOR_PURPLE") &
        OPENOCD_PID=$!

        # For debugging, it may be useful to use `--init-command`, which causes
        # GDB to drop to the interactive prompt when the script ends rather than
        # exiting.
        (/tools/riscv/bin/riscv32-unknown-elf-gdb --command=script.gdb \\
            |& prefix_lines GDB "$COLOR_GREEN") &

        ./opentitantool console \\
            --timeout 15s \\
            --exit-success='{exit_success_pattern}' \\
            |& prefix_lines CONSOLE "$COLOR_RED"

        # Send TERM signal to OpenOCD and wait for all background jobs to complete. Note
        # that GDB will exit naturally at the end of its script.
        kill $OPENOCD_PID
        wait
    '''.format(
        openocd_earlgrey_config = ctx.file._openocd_earlgrey_config.path,
        exit_success_pattern = ctx.attr.exit_success_pattern,
    )

    # Write the GDB script to disk and load it with GDB's `--command` argument.
    # This enables us to separate lines with whitespace, whereas if we piped the
    # string into GDB's stdin, each newline would cause it to repeat the
    # previous command.
    gdb_script_file = ctx.actions.declare_file("{}.gdb".format(ctx.label.name))
    test_script_file = ctx.actions.declare_file("{}.sh".format(ctx.label.name))

    ctx.actions.write(output = gdb_script_file, content = ctx.attr.gdb_script)
    ctx.actions.write(output = test_script_file, content = test_script)

    # Construct a dict that we can pass to `ctx.runfiles()`, mapping symlink
    # names to real file paths.
    gdb_script_symlinks_flipped = {}
    for label in ctx.attr.gdb_script_symlinks:
        label_files = label.files.to_list()
        if len(label_files) != 1:
            fail("gdb_script_symlinks labels must have exactly one file, but", label, "has these files:", label_files)
        gdb_script_symlinks_flipped[ctx.attr.gdb_script_symlinks[label]] = label_files[0]

    gdb_script_runfiles = ctx.runfiles(
        symlinks = gdb_script_symlinks_flipped,
        files = gdb_script_symlinks_flipped.values(),
    )
    test_script_runfiles = ctx.runfiles(
        # Relative paths provided by `File.path` seem to not work
        # for generated files. Symlinking the runtime files wherever
        # Bazel will run `test_script_file` sidesteps the issue.
        symlinks = {
            "opentitantool": ctx.file._opentitantool,
            "rom.bit": ctx.file.rom_bitstream,
            "script.gdb": gdb_script_file,
        },
        files = [
            ctx.file._openocd_earlgrey_config,
            ctx.file._opentitantool,
            ctx.file.rom_bitstream,
            gdb_script_file,
        ],
    )
    runfiles = test_script_runfiles.merge(gdb_script_runfiles)

    return [DefaultInfo(
        executable = test_script_file,
        runfiles = runfiles,
    )]

# Orchestrate opentitantool, OpenOCD, and GDB to load the given program into
# SRAM and execute it in-place. This rule assumes that a CW310 FPGA and an
# ARM-USB-TINY-H JTAG debugger are attached to the host.
opentitan_gdb_fpga_cw310_test = rv_rule(
    implementation = _opentitan_gdb_fpga_cw310_test,
    attrs = {
        "exit_success_pattern": attr.string(mandatory = True),
        "gdb_script": attr.string(mandatory = True),
        "gdb_script_symlinks": attr.label_keyed_string_dict(allow_files = True),
        "rom_bitstream": attr.label(
            mandatory = True,
            allow_single_file = True,
        ),
        "_opentitantool": attr.label(
            default = "//sw/host/opentitantool",
            allow_single_file = True,
            cfg = "exec",
        ),
        "_openocd_earlgrey_config": attr.label(
            default = "//util/openocd/target:lowrisc-earlgrey.cfg",
            allow_single_file = True,
        ),
    },
    test = True,
)
