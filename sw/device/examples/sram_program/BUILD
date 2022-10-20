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
    timeout = "short",
    exit_success_pattern = "sram_program\\.c:\\d+\\] PC: 0x100020e0, SRAM: \\[0x10000000, 0x10020000\\)",
    gdb_script = """
        target extended-remote :3333

        echo :::: Send OpenOCD the 'reset halt' command.\\n
        monitor reset halt


        # Mitigate flakiness from the watchdog timer. Prior to connecting
        # OpenOCD and GDB, the device is executing normally. The ROM has
        # probably already started up and configured the watchdog timer. This is
        # a problem; if the timer fires while we're connected, the interrupt
        # will steal control away from the debugger and cause this test to fail.
        # Thus, we need to disable the watchdog timer as quickly as possible to
        # minimize the chances of it firing.
        #
        # The proper solution would be to disable ROM execution by provisioning
        # with an OTP image that has CREATOR_SW_CFG_ROM_EXEC_EN set to zero.
        #
        # Initialize and disable the watchdog timer per aon_timer docs [1]. The
        # hardcoded addresses were computed by adding REG_OFFSET values from
        # //hw/ip/aon_timer/data:aon_timer_regs to the base address
        # TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR.
        #
        # [1]: https://docs.opentitan.org/hw/ip/aon_timer/doc/#initialization

        echo :::: Disable the watchdog timer.\\n
        monitor mdw 0x40470014
        monitor mww 0x40470014 0
        echo :::: Reset WDOG_COUNT.\\n
        monitor mdw 0x40470020
        monitor mww 0x40470020 0
        echo :::: Clear the interrupt (if any) by writing to INTR_STATE.\\n
        monitor mdw 0x40470024
        monitor mww 0x40470024 0


        # Before transferring the SRAM program to the device, we must configure
        # the PMP unit to enable writing to and executing from SRAM. Due to
        # implementation details of OpenTitan's hardware debug module, we cannot
        # set pmpcfg* registers to arbitrary values [1]. However, we can safely
        # modify unused PMP configuration registers. Thankfully, pmp0cfg (the
        # lowest byte of CSR pmpcfg0) is unused and has the highest priority.
        #
        # In more detail, the problem is that our debug module implements the
        # "Access Register" abstract command by assembling instructions in the
        # program buffer and then executing the buffer. If one of those
        # instructions clobbers the PMP configuration register that allows
        # execution from the program buffer, subsequent instruction fetches will
        # generate exceptions.
        #
        # Debug module concepts like abstract commands and the program buffer
        # buffer are defined in "RISC-V External Debug Support Version 0.13.2"
        # [2]. OpenTitan's (vendored-in) implementation lives in
        # //hw/vendor/pulp_riscv_dbg.
        #
        # [1]: https://github.com/lowRISC/opentitan/issues/14978
        # [2]: https://riscv.org/wp-content/uploads/2019/03/riscv-debug-release.pdf

        echo :::: Configure the PMP unit.\\n
        monitor reg pmpcfg0
        # Write "L NAPOT X W R" to pmp{0,1,2,3}cfg in pmpcfg0. Crucially, this
        # value is no less permissive than whatever the current value is.
        monitor reg pmpcfg0 0x9f9f9f9f
        monitor reg pmpaddr0 0xffffffff

        echo :::: Value of CREATOR_SW_CFG_ROM_EXEC_EN.\\n
        monitor mdw 0x40131108

        echo :::: Load the SRAM program onto the device and check integrity.\\n
        file sram_program.elf
        load sram_program.elf
        compare-sections

        echo :::: Update registers before calling functions.\\n
        set $sp = _stack_end
        set $gp = __global_pointer$
        info registers

        # When testing SRAM execution, we want to be sure the code is running
        # out of SRAM and not the instruction cache.
        echo :::: Invalidate the icache.\\n
        print icache_invalidate()

        echo :::: Call sram_main().\\n
        print sram_main()

        echo :::: Done.\\n
    """,
    gdb_script_symlinks = {
        ":sram_program_fpga_cw310.elf": "sram_program.elf",
        "//sw/device/silicon_creator/rom:rom_fpga_cw310.elf": "rom.elf",
    },
    rom_bitstream = "//hw/bitstream:rom_otp_exec_disabled",
    rom_kind = "Rom",
    tags = ["manual"],
)
