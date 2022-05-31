Ibex simulation for RISC-V Compliance Testing
=============================================

This directory contains a compiled simulation of Ibex to be used as target
in the [RISC-V Compliance Test](https://github.com/riscv/riscv-compliance).
In addition to Ibex itself, it contains a 64 kB RAM and a memory-mapped helper
module to interact with the software, e.g. to dump out the test signature and to
end the simulation.

The simulation is designed for Verilator, but can be adapted to other simulators
if needed.

How to run RISC-V Compliance on Ibex
------------------------------------

0. Check your prerequisites
   To compile the simulation and run the compliance test suite you need to
   have the following tools installed:
   - Verilator
   - fusesoc
   - srecord (for `srec_cat`)
   - A RV32 compiler

   On Ubuntu/Debian, install the required tools like this:

   ```sh
   sudo apt-get install srecord python3-pip
   pip3 install --user -U fusesoc
   ```

   We recommend installing Verilator from source as versions from Linux
   distributions are often outdated. See
   https://www.veripool.org/projects/verilator/wiki/Installing for installation
   instructions.

1. Build a simulation of Ibex

   ```sh
   cd $IBEX_REPO_BASE
   fusesoc --cores-root=. run --target=sim --setup --build lowrisc:ibex:ibex_riscv_compliance --RV32E=0 --RV32M=ibex_pkg::RV32MNone
   ```

   You can use the two compile-time options `--RV32M` and `--RV32E` to
   enable/disable the M and E ISA extensions, respectively.

   You can now find the compiled simulation at `build/lowrisc_ibex_ibex_riscv_compliance_0.1/sim-verilator/Vibex_riscv_compliance`.

2. Get the RISC-V Compliance test suite

   The upstream RISC-V compliance test suite supports Ibex out of the box.

   ```
   git clone https://github.com/riscv/riscv-compliance.git
   cd riscv-compliance
   ```

3. Run the test suite
   ```sh
   cd $RISCV_COMPLIANCE_REPO_BASE
   # adjust to match your compiler name
   export RISCV_PREFIX=riscv32-unknown-elf-
   # give the absolute path to the simulation binary compiled in step 1
   export TARGET_SIM=/path/to/your/Vibex_riscv_compliance

   export RISCV_DEVICE=rv32imc
   export RISCV_TARGET=ibex

   # Note: rv32imc does not include the I and M extension tests
   make RISCV_ISA=rv32i && make RISCV_ISA=rv32im && make RISCV_ISA=rv32imc && \
      make RISCV_ISA=rv32Zicsr && make RISCV_ISA=rv32Zifencei
   ```

Compliance test suite system
----------------------------

This directory contains a system designed especially to run the compliance test
suite. The system consists of

- an Ibex core,
- a bus,
- a single-port memory for data and instructions,
- a bus-attached test utility.

The CPU core boots from SRAM at address 0x0.

The test utility is used by the software to end the simulation, and to inform
the simulator of the memory region where the test signature is stored.
The bus host reads the test signature from memory.

The memory map of the whole system is as follows:

| Start   | End     | Size  | Device                         |
|---------|---------|-------|--------------------------------|
| 0x0     | 0xFFFF  | 64 kB | shared instruction/data memory |
| 0x20000 | 0x203FF | 1 kB  | test utility                   |


The test utility provides the following registers relative to the base address.

| Address | R/W | Description                                                         |
|---------|-----|---------------------------------------------------------------------|
| 0x0     | W   | Write any value to dump the test signature and terminate simulation |
| 0x4     | W   | Start address of the test signature                                 |
| 0x8     | W   | End address of the test signature                                   |
