# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "opentitan_ram_binary")
load("//rules:opentitan_gdb_test.bzl", "opentitan_gdb_fpga_cw310_test")
load("//rules:linker.bzl", "ld_library")

package(default_visibility = ["//visibility:public"])

ld_library(
    name = "sram_program_linker_script",
    script = "sram_program.ld",
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
        "//sw/device:info_sections",
        "//sw/device/silicon_creator/lib/base:static_critical_sections",
    ],
)

opentitan_ram_binary(
    name = "sram_program",
    srcs = [
        "sram_program.c",
    ],
    hdrs = [
        "sram_program.h",
    ],
    archive_symbol_prefix = "sram_program",
    deps = [
        ":sram_program_linker_script",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/test_framework:check",
    ],
)

opentitan_gdb_fpga_cw310_test(
    name = "sram_program_fpga_cw310_test",
    exit_success_pattern = "sram_program\\.c:47\\] PC: 0x1000208c, SRAM: \\[0x10000000, 0x10020000\\)",
    gdb_script = """
        target extended-remote :3333
        set pagination off

        echo :::: Send OpenOCD the 'reset halt' command.\\n
        monitor reset halt

        echo :::: Set RAM as RWX by executing code between _start and test_rom_main()\\n
        file test_rom.elf
        break rom_test_main
        continue
        delete breakpoints

        echo :::: Load the SRAM program onto the device and check integrity.\\n
        file sram_program.elf
        load sram_program.elf
        compare-sections

        info registers
        echo :::: Update registers before calling sram_main().\\n
        set $sp = _stack_end
        set $gp = __global_pointer$
        info registers

        echo :::: Call sram_main().\\n
        print sram_main()

        echo :::: Done.\\n
    """,
    gdb_script_symlinks = {
        ":sram_program_fpga_cw310.elf": "sram_program.elf",
        "//sw/device/lib/testing/test_rom:test_rom_fpga_cw310.elf": "test_rom.elf",
    },
    # TODO(#13968) Switch to ROM instead of Test ROM.
    rom_bitstream = "//hw/bitstream:test_rom",
    tags = ["manual"],
)
