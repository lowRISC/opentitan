# OpenTitan Big Number Accelerator (OTBN)

This directory contains the implementation of the OpenTitan Big Number
Accelerator (OTBN). OTBN is a coprocessor for asymmetric cryptographic
operations like RSA or Elliptic Curve Cryptography (ECC).

See https://docs.opentitan.org/hw/ip/otbn/doc/index.html for documentation on
the current version of OTBN; documentation matching the code in this directory
can be found in the `doc` directory.

OTBN is under active development. Please ask questions and report issues
through the [GitHub issue tracker](https://github.com/lowRISC/opentitan/issues).

## Develop OTBN

### Build OTBN software

An assembler, linker and disassembler for OTBN can be found in
`hw/ip/otbn/util`. These are wrappers around a RISC-V GCC and binutils toolchain
so one must be available (see the OpenTitan documentation on [obtaining a
toolchain](https://docs.opentitan.org/doc/ug/install_instructions/#software-development).
For more details about the toolchain, see the [user
guide](https://docs.opentitan.org/doc/ug/otbn_sw)).

`otbn-as` and `otbn-ld` can be used to build .elf files for use with
simulations. They work work similarly to binutils programs they wrap.

```
hw/ip/otbn/util/otbn-as -o prog_bin/prog.o prog.s
hw/ip/otbn/util/otbn-ld -o prog_bin/prog.elf prog_bin/prog.o
```

Will assemble and link `prog.s` resulting in `prog_bin/prog.elf` that can be run
directly on the ISS or the standalone RTL simulation.

### Work with the ISA

The instruction set is described in machine readable form in
`data/insns.yml`. This is parsed by Python code in
`util/insn_yaml.py`, which runs various basic checks on the data. The
binutils-based toolchain described above uses this information. Other
users include:

  - `util/yaml_to_doc.py`: Generates a Markdown snippet which is included in
    the OTBN specification.

  - `dv/rig/otbn-rig`: A random instruction generator for OTBN. See
    dv/rig/README.md for further information.

### Run the standalone RTL simulation
A standalone environment to run OTBN alone in Verilator is included. Build it
with `fusesoc` as follows:

```sh
fusesoc --cores-root=. run --target=sim --setup --build lowrisc:ip:otbn_top_sim
```

It includes functionality to set the initial Dmem and Imem contents from a .elf
file. The start address is hard coded to 0. Modify the `ImemStartAddr` parameter
in `./dv/verilator/otbn_top_sim.sv` to change this. A .elf (see above for build
instructions) can be loaded and run as follows:

```sh
./build/lowrisc_ip_otbn_top_sim_0.1/sim-verilator/Votbn_top_sim \
  --load-elf=prog_bin/prog.elf
```

The simulation automatically halts on an `ecall` instruction and prints the
final register values. The ISS is run in parallel and final register and memory
state will be cross-checked.

Tracing functionality is available in the `Votbn_top_sim` binary. To obtain a
full .fst wave trace pass the `-t` flag. To get an instruction level trace pass
the `--otbn-trace-file=trace.log` argument. The instruction trace format is
documented in `hw/ip/otbn/dv/tracer`.

### Run the smoke test

A smoke test which exercises some functionality of OTBN can be found, together
with its expected outputs (in the form of final register values), in
`./hw/ip/otbn/dv/smoke`. The test can be run using a script.

```sh
hw/ip/otbn/dv/smoke/run_smoke.sh
```

This will build the standalone simulation, build the smoke test binary, run it
and check the results are as expected.

### Run OT earlgrey simulation with the OTBN model, rather than the RTL design

For simulation targets, the OTBN block can be built with both the RTL
implementation and the Python-based instruction set simulator (hereafter called
the ISS) compiled in. When running the simulation the plusarg `OTBN_USE_MODEL`
can be used to switch between the RTL implementation and the model, without
recompiling the simulation.

The Verilator simulation of Earl Grey (`lowrisc:systems:top_earlgrey_verilator`)
builds the model by default when compiling the simulation and nothing else needs
to be done. For other simulation targets, set the `OTBN_BUILD_MODEL` define,
e.g. by passing `--OTBN_BUILD_MODEL` to fusesoc.

To run the simulation against the OTBN ISS pass `+OTBN_USE_MODEL=1` to the
simulation run, e.g.

```sh
build/lowrisc_systems_top_earlgrey_verilator_0.1/sim-verilator/Vtop_earlgrey_verilator \
  --meminit=rom,build-bin/sw/device/boot_rom/boot_rom_sim_verilator.elf  \
  --meminit=flash,build-bin/sw/device/tests/dif_otbn_smoketest_sim_verilator.elf \
  --meminit=otp,build-bin/sw/device/otp_img/otp_img_sim_verilator.vmem \
  +UARTDPI_LOG_uart0=- \
  +OTBN_USE_MODEL=1
```

The simulation communicates with the model by creating a directory in
the temporary directory (/tmp or TMPDIR) and filling it with files.
Normally, it cleans up after itself. If something goes wrong and you'd
like to look at these files, set the `OTBN_MODEL_KEEP_TMP` environment
variable to `1`.

### Run the ISS on its own

There are currently two versions of the ISS and they can be found in
`dv/otbnsim`. The easiest to use is `dv/otbnsim/standalone.py`. This
takes an OTBN binary as an ELF file (as produced by the standard
linker script for `otbn-ld`) and can dump the resulting DMEM if given
the `--dmem-dump` argument. To see an instruction trace, pass the
`--verbose` flag.

There is also `dv/otbnsim/otbnsim.py`. This takes flat binary files
with the contents of IMEM and DMEM and, when finished, generates a
cycle count and dumps DMEM contents. This is used to implement the
model inside of simulation, but is probably not very convenient for
command-line use otherwise.

## Test the ISS

The ISS has a simple test suite, which runs various instructions and
makes sure they behave as expected. You can find the tests in
`dv/otbnsim/test` and can run them with `make -C dv/otbnsim test`.

