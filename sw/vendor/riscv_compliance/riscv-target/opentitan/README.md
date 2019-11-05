---
title: "OpenTitan RISC-V Compliance Testing"
---

# Overview
The RISC-V compliance test can be run on either FPGA or Verilator.
To run on Verilator, set the variables below

```console
$ export RISCV_TARGET=opentitan
$ export RISCV_DEVICE=rv32imc
$ export TARGET=verilator
```

To run on FPGA, set the variables below.
The `FPGA_UART` variable must be set to wherever a valid device is connected.

```console
$ export RISCV_TARGET=opentitan
$ export RISCV_DEVICE=rv32imc
$ export TARGET=fpga
$ export FPGA_UART=/dev/tty*
```

By default, the test assumes there exists a valid Verilator build at `${REPO_TOP}/build/lowrisc_systems_top_earlgrey_verilator_0.1/sim-verilator/Vtop_earlgrey_verilator`.
If your Verilator build is at a different location, please set that as well when running with Verilator.
For instructions on how to create a Verilator build, please refer to the [Verilator guide]({{< relref "doc/ug/getting_started_verilator" >}}).

```console
$ export TARGET_SIM=${PATH_TO_VERILATOR_BUILD}
```

When running against FPGA, the test assumes the FPGA is already programmed and ready to go.
To find out how to properly build and flash FPGA, please refer to the [FPGA manual]({{< relref "doc/rm/ref_manual_fpga" >}})


Now, run the tests.
The following output will be seen (software build steps are truncated).
The example below uses Verilator as an example, but the FPGA output is nearly identical.

```console
$ cd $REPO_TOP
$ make -C sw/vendor/riscv_compliance RISCV_ISA=rv32i \
  && make -C sw/vendor/riscv_compliance RISCV_ISA=rv32im \
  && make -C sw/vendor/riscv_compliance RISCV_ISA=rv32imc


Rom initialized with program at $REPO_TOP/sw/vendor/riscv_compliance/../../boot_rom/rom.vmem

Flash initialized with program at $REPO_TOP/sw/vendor/riscv_compliance/work/rv32i/I-ENDIANESS-01.elf.vmem

JTAG: Virtual JTAG interface jtag0 is listening on port 44853. Use
OpenOCD and the following configuration to connect:
  interface remote_bitbang
  remote_bitbang_host localhost
  remote_bitbang_port 44853

SPI: Created /dev/pts/21 for spi0. Connect to it with any terminal program, e.g.
$ screen /dev/pts/21
NOTE: a SPI transaction is run for every 4 characters entered.
SPI: Monitor output file created at $REPO_TOP/sw/vendor/riscv_compliance/riscv-test-suite/rv32i/spi0.log. Works well with tail:
$ tail -f $REPO_TOP/sw/vendor/riscv_compliance/riscv-test-suite/rv32i/spi0.log

UART: Created /dev/pts/22 for uart0. Connect to it with any terminal program, e.g.
$ screen /dev/pts/22

Simulation running, end by pressing CTRL-c.
TOP.top_earlgrey_verilator.top_earlgrey.core.ibex_tracer_i: Writing execution trace to trace_core_00000000.log
Verilator sim termination requested
Your simulation wrote to 0x10008000

...

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
Check       I-CSRRC-01 ... OK
Check      I-CSRRCI-01 ... OK
Check       I-CSRRS-01 ... OK
Check      I-CSRRSI-01 ... OK
Check       I-CSRRW-01 ... OK
Check      I-CSRRWI-01 ... OK
Check I-DELAY_SLOTS-01 ... OK
Check      I-EBREAK-01 ... OK
Check       I-ECALL-01 ... OK
Check   I-ENDIANESS-01 ... OK
Check     I-FENCE.I-01 ... OK
Check             I-IO ... OK
Check         I-JAL-01 ... OK
Check        I-JALR-01 ... OK
Check          I-LB-01 ... OK
Check         I-LBU-01 ... OK
Check          I-LH-01 ... OK
Check         I-LHU-01 ... OK
Check         I-LUI-01 ... OK
Check          I-LW-01 ... OK
Check I-MISALIGN_JMP-01 ... OK
Check I-MISALIGN_LDST-01 ... OK
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
OK: 55/55


```
