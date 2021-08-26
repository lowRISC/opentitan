# Ibex RISC-V Core SoC Example

Please see [examples](https://ibex-core.readthedocs.io/en/latest/02_user/examples.html "Ibex User Manual") for a description of this example.

## Requirements

### Tools

  - RV32 compiler
  - srecord
  - `fusesoc` and its dependencies
  - Xilinx Vivado

### Hardware

  - Either a Digilent Arty A7-35 oder A7-100 board

## Build

The easiest way to build and execute this example is to call the following make goals from the root directory.

Use the following for the Arty A7-35

```
make build-arty-35 program-arty
```

and for the Arty A7-100

```
make build-arty-100 program-arty
```

### Software

First the software must be built. Go into `examples/sw/led` and call:

```
make CC=/path/to/RISC-V-compiler
```

The setting of `CC` is only required if `riscv32-unknown-elf-gcc` is not available through the `PATH` environment variable.
The path to the RV32 compiler `/path/to/RISC-V-compiler` depends on the environment.
For example, it can be for example `/opt/riscv/bin/riscv-none-embed-gcc` if the whole path is required or simply the name of the executable if it is available through the `PATH` environment variable.

This should produce a `led.vmem` file which is used in the synthesis to update the SRAM storage.



### Hardware

Run either of the following commands at the top level to build the respective hardware.
Both variants of the Arty A7 are supported and can be selected via the `--parts` parameter.

```
fusesoc --cores-root=. run --target=synth --setup --build lowrisc:ibex:top_artya7 --part xc7a35ticsg324-1L
```

```
fusesoc --cores-root=. run --target=synth --setup --build lowrisc:ibex:top_artya7 --part xc7a100tcsg324-1
```

This will create a directory `build` which contains the output files, including
the bitstream.


Initial memory parameter `SRAMInitFile` can be given to FuseSoc to specify which .vmem file to load the design with.
Example use case includes loading `coremark.vmem` which can be used for performance/power analysis.

Please see [CoreMark README](https://github.com/lowRISC/ibex/blob/master/examples/sw/benchmarks/README.md) for compiling CoreMark.

```
fusesoc --cores-root=. run --target=synth --setup --build lowrisc:ibex:top_artya7 --part xc7a100tcsg324-1 --SRAMInitFile=examples/sw/benchmarks/coremark/coremark.vmem
```

#### Power Analysis Using Vivado

Setting `FPGAPowerAnalysis` parameter to 1 allows user to run a power analysis using Vivado.
It uses a post-implementation functional simulation on Vivado to log switching activity.
This switching activity is then used to generate a detailed power report.
In order to use it with CoreMark run the command below

```
fusesoc --cores-root=. run --target=synth --setup --build lowrisc:ibex:top_artya7 --part xc7a100tcsg324-1 --SRAMInitFile=examples/sw/benchmarks/coremark/coremark.vmem --FPGAPowerAnalysis=1
```

## Program

After the board is connected to the computer it can be programmed with:

```
fusesoc --cores-root=. run --target=synth --run lowrisc:ibex:top_artya7
```

LED1/LED3 and LED0/LED2 should alternately be on after the FPGA programming is finished.
