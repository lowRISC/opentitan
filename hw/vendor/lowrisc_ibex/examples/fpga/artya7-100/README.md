# Ibex RISC-V Core SoC Example

Please see [examples](https://ibex-core.readthedocs.io/en/latest/examples.html "Ibex User Manual") for a description of this example.

## Requirements

### Tools

  - RV32 compiler
  - srecord
  - `fusesoc` and its dependencies
  - Xilinx Vivado

## Build

### Software

First the software must be built. Go into `examples/sw/led` and call:

```
make CC=/path/to/RISC-V-compiler
```

The path to the RV32 compiler `/path/to/RISC-V-compiler` depends on the environment.
For example, it can be `riscv32-unknown-elf-gcc` if the binary is available through the `PATH` environment or `/opt/riscv/bin/riscv-none-embed-gcc` if a specific path is used.

This should produce a `led.vmem` file which is used in the synthesises to update the SRAM storage.

### Hardware

Run the following command at the top level to build the hardware.

```
fusesoc --cores-root=. run --target=synth --setup --build lowrisc:ibex:top_artya7_100
```

This will create a directory `build` which contains the output files, including
the bitstream.

## Program

After the board is connected to the computer it can be programmed with:

```
fusesoc --cores-root=. pgm lowrisc:ibex:top_artya7_100
```

LED1/LED3 and LED0/LED2 should alternately be on after the FPGA programming is finished.
