# Ibex Simple System with Co-simulation checking

This augments the Ibex Simple System (`examples/simple_system`) to include the
co-simulation system to check Ibex's execution. This runs Spike in lockstep with
Ibex and checks each instruction Ibex retires matches what Spike has executed.
In addition all data memory accesses are checked against memory acceses Spike
has performed. More details on how the co-simulation works and how to build and
run simple system with it included can be in found in the Ibex documentation
under 'Co-simulation System' in the 'Ibex Reference Guide' section.

## Quick Build and Run Instructions

```
# Get the Ibex co-simulation spike branch
git clone -b ibex_cosim https://github.com/lowRISC/riscv-isa-sim.git riscv-isa-sim-cosim

# Setup build directory
cd riscv-isa-sim-cosim
mkdir build
cd build

# Configure and build spike
../configure --enable-commitlog --enable-misaligned --prefix=/opt/spike-cosim 
# Installs in /opt/spike-cosim
sudo make -j8 install

# Setup PKG_CONFIG_PATH so pkg-config can find libs and cflags for the cosim
export PKG_CONFIG_PATH=/opt/spike-cosim/lib/pkgconfig:$PKG_CONFIG_PATH

# Switch to a checkout of the Ibex repository
cd <ibex_repo>

# Build simulator
fusesoc --cores-root=. run --target=sim --setup --build lowrisc:ibex:ibex_simple_system_cosim --RV32E=0 --RV32M=ibex_pkg::RV32MFast

# Build coremark test binary, with performance counter dump disabled. The 
# co-simulator system doesn't produce matching performance counters in spike so
# any read of those CSRs results in a mismatch and a failure.
make -C ./examples/sw/benchmarks/coremark SUPPRESS_PCOUNT_DUMP=1

# Run coremark binary with co-simulation checking
build/lowrisc_ibex_ibex_simple_system_cosim_0/sim-verilator/Vibex_simple_system --meminit=ram,examples/sw/benchmarks/coremark/coremark.elf
```

Sample output:

```
Simulation of Ibex
==================

Tracing can be toggled by sending SIGUSR1 to this process:
$ kill -USR1 29121

Simulation running, end by pressing CTRL-c.
TOP.ibex_simple_system.u_top.u_ibex_tracer.unnamedblk1: Writing execution trace to trace_core_00000000.log
Terminating simulation by software request.
- ../src/lowrisc_ibex_sim_shared_0/./rtl/sim/simulator_ctrl.sv:93: Verilog $finish
Received $finish() from Verilog, shutting down simulation.

Simulation statistics
=====================
Executed cycles:  4116797
Wallclock time:   17.053 s
Simulation speed: 241412 cycles/s (241.412 kHz)
Co-simulation matched 2789425 instructions

Performance Counters
====================
Cycles:                     4055056
NONE:                       0
Instructions Retired:       2750348
LSU Busy:                   684533
Fetch Wait:                 187543
Loads:                      541082
Stores:                     143451
Jumps:                      57169
Conditional Branches:       523452
Taken Conditional Branches: 187543
Compressed Instructions:    0
Multiply Wait:              187920
Divide Wait:                0
```
