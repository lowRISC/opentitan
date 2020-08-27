# Ibex Simple System

Simple System gives you an Ibex based system simulated by Verilator that can
run stand-alone binaries. It contains:

* An Ibex Core
* A single memory for instructions and data
* A basic peripheral to write ASCII output to a file and halt simulation from software
* A basic timer peripheral capable of generating interrupts based on the RISC-V Machine Timer Registers (see RISC-V Privileged Specification, version 1.11, Section 3.1.10)
* A software framework to build programs for it

## Prerequisites

* [Verilator](https://www.veripool.org/wiki/verilator)
  Note Linux package managers may have Verilator but often a very old version
  that is not suitable. It is recommended Verilator is built from source.
* The Python dependencies of this repository.
  Install them with `pip3 install -U python3-requirements.txt` from the
  repository root.
* RISC-V Compiler Toolchain - lowRISC provides a pre-built GCC based toolchain
  <https://github.com/lowRISC/lowrisc-toolchains/releases>
* libelf and its development libraries.
  On Debian/Ubuntu, install it by running `apt-get install libelf-dev`.

## Building Simulation

The Simple System simulator binary can be built via FuseSoC. From the Ibex
repository root run:

```
fusesoc --cores-root=. run --target=sim --setup --build lowrisc:ibex:ibex_simple_system --RV32E=0 --RV32M=ibex_pkg::RV32MFast
```

## Building Software

Simple System related software can be found in `examples/sw/simple_system`.

To build the hello world example, from the Ibex reposistory root run:

```
make -C examples/sw/simple_system/hello_test
```

The compiled program is available at
`examples/sw/simple_system/hello_test/hello_test.elf`. The same directory also
contains a Verilog memory file (vmem file) to be used with some simulators.

To build new software make a copy of the `hello_test` directory named as desired.
Look inside the Makefile for further instructions.

If using a toolchain other than the lowRISC pre-built one
`examples/sw/simple_system/common/common.mk` may need altering to point to the
correct compiler binaries.

## Running the Simulator

Having built the simulator and software, from the Ibex repository root run:

```
./build/lowrisc_ibex_ibex_simple_system_0/sim-verilator/Vibex_simple_system [-t] --meminit=ram,<sw_elf_file>
```

`<sw_elf_file>` should be a path to an ELF file  (or alternatively a vmem file)
built as described above. Use
`./examples/sw/simple_system/hello_test/hello_test.elf` to run the `hello_test`
binary.

Pass `-t` to get an FST trace of execution that can be viewed with
[GTKWave](http://gtkwave.sourceforge.net/). If using the `hello_test`
binary the simulator will halt itself, outputting some simulation
statistics:

```
Simulation statistics
=====================
Executed cycles:  633
Wallclock time:   0.013 s
Simulation speed: 48692.3 cycles/s (48.6923 kHz)

Performance Counters
====================
Cycles:                     483
NONE:                       0
Instructions Retired:       266
LSU Busy:                   59
Fetch Wait:                 16
Loads:                      21
Stores:                     38
Jumps:                      46
Conditional Branches:       53
Taken Conditional Branches: 48
Compressed Instructions:    182
```

The simulator produces several output files

* `ibex_simple_system.log` - The ASCII output written via the output peripheral
* `ibex_simple_system_pcount.csv` - A CSV of the performance counters
* `trace_core_00000000.log` - An instruction trace of execution

## Simulating with Synopsys VCS

Similar to the Verilator flow the Simple System simulator binary can be built using:

```
fusesoc --cores-root=. run --target=sim --tool=vcs --setup --build lowrisc:ibex:ibex_simple_system --RV32E=0 --RV32M=ibex_pkg::RV32MFast --SRAMInitFile=`<sw_vmem_file>`
```

`<sw_vmem_file>` should be a path to a vmem file built as described above, use
`./examples/sw/simple_system/hello_test/hello_test.vmem` to run the `hello_test`
binary.

To run the simulator:

```
./build/lowrisc_ibex_ibex_simple_system_0/sim-vcs/lowrisc_ibex_ibex_simple_system_0
```

Pass `-gui` to use the DVE GUI.

## Simulating with Riviera-PRO

To build and run Simple System run:

```
fusesoc --cores-root=. run --target=sim --tool=rivierapro lowrisc:ibex:ibex_simple_system --RV32E=0 --RV32M=ibex_pkg::RV32MFast --SRAMInitFile=\"$(readlink -f <sw_vmem_file>)\"
```

`<sw_vmem_file>` should be a path to a vmem file built as described above, use
`./examples/sw/simple_system/hello_test/hello_test.vmem` to run the `hello_test`
binary.

## System Memory Map

| Address             | Description                                                                                            |
|---------------------|--------------------------------------------------------------------------------------------------------|
| 0x20000             | ASCII Out, write ASCII characters here that will get output to the log file                            |
| 0x20008             | Simulator Halt, write 1 here to halt the simulation                                                    |
| 0x30000             | RISC-V timer `mtime` register                                                                          |
| 0x30004             | RISC-V timer `mtimeh` register                                                                         |
| 0x30008             | RISC-V timer `mtimecmp` register                                                                       |
| 0x3000C             | RISC-V timer `mtimecmph` register                                                                      |
| 0x100000 – 0x1FFFFF | 1 MB memory for instruction and data. Execution starts at 0x100080, exception handler base is 0x100000 |
