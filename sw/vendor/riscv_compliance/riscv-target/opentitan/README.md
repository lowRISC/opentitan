
# Overview
The RISC-V compliance test can be run on either OpenTitan FPGA or Verilator.
OpenTitan is an open source project to build transparent, high-quality reference designs for silicon root of trust chips.
Please see the [OpenTitan website](https://opentitan.org) for more details.

To run on Verilator, set the variables below

```console
$ export RISCV_TARGET=opentitan
$ export RISCV_DEVICE=rv32imc
$ export OT_TARGET=verilator
```

To run on FPGA, set the variables below.
The `FPGA_UART` variable must be set to wherever a valid device is connected.

```console
$ export RISCV_TARGET=opentitan
$ export RISCV_DEVICE=rv32imc
$ export OT_TARGET=fpga
$ export OT_FPGA_UART=/dev/tty*
```

By default, the test assumes there exists a valid Verilator build at `${REPO_TOP}/build/lowrisc_systems_top_earlgrey_verilator_0.1/sim-verilator/Vtop_earlgrey_verilator`.
If your Verilator build is at a different location, please set that as well when running with Verilator.

```console
$ export TARGET_SIM=${PATH_TO_VERILATOR_BUILD}
```

When running against FPGA, the test assumes the FPGA is already programmed and ready to go.
To quickly get started with a verilator binary or FPGA bitfile, please see the [OpenTitan quick start guide](https://docs.opentitan.org/doc/ug/quickstart/)


Now, run the tests from the riscv_compliance directory.
The following output will be seen (software build steps are truncated).
The example below uses Verilator as an example, but the FPGA output is nearly identical.

```console
$ cd $RISCV_COMPLIANCE_REPO_BASE
$ make RISCV_ISA=rv32i \
  && make RISCV_ISA=rv32im \
  && make RISCV_ISA=rv32imc


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

...

--------------------------------
OK: 55/55


```


## Removed Tests
A small number of tests are not run for OpenTitan riscv_compliance since the underlying core does not yet support specific features.
The removed tests are the following:

* I-MISALIGN_JMP-01
* I-MISALIGN_LDST-01
* I-FENCE.I-01
* I-ECALL-01
* I-EBREAK-01
