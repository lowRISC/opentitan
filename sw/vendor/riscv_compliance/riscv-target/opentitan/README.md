
# Overview
The RISC-V compliance test can be run on either OpenTitan FPGA or Verilator.
OpenTitan is an open source project to build transparent, high-quality reference
designs for silicon root of trust chips.  Please see the [OpenTitan
website](https://opentitan.org) for more details.

To run on Verilator, set the variables below

```console
$ export RISCV_TARGET=opentitan
$ export RISCV_DEVICE=rv32imc
$ export OT_TARGET=sim_verilator
```

To run on FPGA, set the variables below.  The `OT_FPGA_UART` variable must be
set to wherever a valid device is connected.

```console
$ export RISCV_TARGET=opentitan
$ export RISCV_DEVICE=rv32imc
$ export OT_TARGET=fpga_nexysvideo
$ export OT_FPGA_UART=/dev/tty*
```

By default, the test assumes there exists a valid Verilator build at
`${REPO_TOP}/build/lowrisc_systems_top_earlgrey_verilator_0.1/sim-verilator/Vtop_earlgrey_verilator`.
If your Verilator build is at a different location, please set that as well when
running with Verilator.

```console
$ export TARGET_SIM=${PATH_TO_VERILATOR_BUILD}
```

When running against FPGA, the test assumes the FPGA is already programmed and
ready to go with spiflash available at `$BIN_DIR/sw/host/spiflash/spiflash`.
To quickly get started with a verilator binary or FPGA bitfile, please see the
[OpenTitan quick start guide](https://docs.opentitan.org/doc/ug/quickstart/).

Finally the support software must be built, including the boot_rom when using
the verilator target.

```console
$ cd $REPO_TOP
$ ./meson_init.sh
$ ninja -C ./build-out all
```

Now, run the tests from the riscv_compliance directory.  The following output
will be seen (software build steps are truncated).  The example below uses
Verilator as an example, but the FPGA output is nearly identical.

```console
$ cd $RISCV_COMPLIANCE_REPO_BASE
$ make RISCV_ISA=rv32i

... verbose test output ...

Compare to reference files ...

Check         I-ADD-01 ... OK
Check        I-ADDI-01 ... OK
Check         I-AND-01 ... OK
Check        I-ANDI-01 ... OK
Check       I-AUIPC-01 ... OK
Check         I-BEQ-01 ... OK
Check         I-BGE-01 ... OK
Check        I-BGEU-01 ... OK
Check         I-BLT-01 ... OK
Check        I-BLTU-01 ... OK
Check         I-BNE-01 ... OK
Check I-DELAY_SLOTS-01 ... OK
Check      I-EBREAK-01 ... OK
Check       I-ECALL-01 ... OK
Check   I-ENDIANESS-01 ... OK
Check          I-IO-01 ... OK
Check         I-JAL-01 ... OK
Check        I-JALR-01 ... OK
Check          I-LB-01 ... OK
Check         I-LBU-01 ... OK
Check          I-LH-01 ... OK
Check         I-LHU-01 ... OK
Check         I-LUI-01 ... OK
Check          I-LW-01 ... OK
Check I-MISALIGN_JMP-01 ... IGNORE
Check I-MISALIGN_LDST-01 ... IGNORE
Check         I-NOP-01 ... OK
Check          I-OR-01 ... OK
Check         I-ORI-01 ... OK
Check     I-RF_size-01 ... OK
Check    I-RF_width-01 ... OK
Check       I-RF_x0-01 ... OK
Check          I-SB-01 ... OK
Check          I-SH-01 ... OK
Check         I-SLL-01 ... OK
Check        I-SLLI-01 ... OK
Check         I-SLT-01 ... OK
Check        I-SLTI-01 ... OK
Check       I-SLTIU-01 ... OK
Check        I-SLTU-01 ... OK
Check         I-SRA-01 ... OK
Check        I-SRAI-01 ... OK
Check         I-SRL-01 ... OK
Check        I-SRLI-01 ... OK
Check         I-SUB-01 ... OK
Check          I-SW-01 ... OK
Check         I-XOR-01 ... OK
Check        I-XORI-01 ... OK
--------------------------------
OK: 48/48
```

There are several test suites that can be run `rv32i`, `rv32im`, `rv32imc` and
`rv32Zicsr`.  Change the `RISCV_ISA` argument passed to `make` to choose between
them.

## Changing targets
When switching between targets (i.e. between FPGA and verilator) the `work`
directory in the `riscv_compliance` tree must be remove to force a software
rebuild.

```console
$ cd $RISCV_COMPLIANCE_REPO_BASE
$ rm -rf ./work
```

## Parallel runs
When running against the `sim_verilator` target parallel make jobs are used (via
passing `-j4` to make internally).  Parallel runs can be disabled by passing
`PARALLEL=0` to the `make` command or the `-j` used can be altered with the
`JOBS` argument.

Disable parallel runs:
```console
$ make RISCV_ISA=rv32i PARALLEL=0
```

Use a different `-j` parameter:
```console
$ make RISCV_ISA=rv32i JOBS=-j8
```

## Removed/Broken Tests
A small number of tests are not run for OpenTitan riscv_compliance as they fail
due to flaws in the compliance test suite rather than Ibex/OpenTitan itself (see
https://github.com/lowRISC/ibex/issues/100). The I-FENCE.I-01 test attempts to
write instruction memory which fails in the OT system as this writes to flash
which can't be done.

* I-MISALIGN_JMP-01
* I-MISALIGN_LDST-01
* I-FENCE.I-01
