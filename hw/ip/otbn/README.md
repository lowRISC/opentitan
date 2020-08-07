# OpenTitan Big Number Accelerator (OTBN)

This directory contains the implementation of the OpenTitan Big Number
Accelerator (OTBN). OTBN is a coprocessor for asymmetric cryptographic
operations like RSA or Elliptic Curve Cryptography (ECC).

See https://docs.opentitan.org/hw/ip/otbn/doc/index.html for documentation on
the current version of OTBN; documentation matching the code in this directory
can be found in the `doc` directory.

OTBN is currently in early development. Please ask questions and report issues
through the [GitHub issue tracker](https://github.com/lowRISC/opentitan/issues).

## Develop OTBN

### Build OTBN software

*Note the toolchain is still under active development. Full OTBN ISA support
isn't complete*

An assembler, linker and disassembler for OTBN can be found in
`hw/ip/otbn/util`. These are wrappers around a RISC-V GCC and binutils toolchain
so one must be available (see the OpenTitan documentation on [obtaining a
toolchain](https://docs.opentitan.org/doc/ug/install_instructions/#software-development).
For more details about the toolchain, see the [user
guide](https://docs.opentitan.org/doc/ug/otbn_sw)).

`hw/ip/otbn/util/build.sh` provides a simple script to build a single OTBN
assembly files using the toolchain:

```sh
hw/ip/otbn/util/build.sh prog.S prog_bin/prog
```

Will assemble and link `prog.S` and produce various outputs using
`prog_bin/prog` as a prefix for all output filenames. Run
`./hw/ip/otbn/util/build.sh` without arguments for more information.

### Run the standalone simulation
*Note that OTBN is still in the early development stages so this simulation does
not support the full ISA*

A standalone environment to run OTBN alone in verilator is included. Build it
with `fusesoc` as follows:

```sh
fusesoc --cores-root=. run --target=sim --setup --build lowrisc:ip:otbn_top_sim
```

It includes functionality to set the initial DMem and IMem contents. The start
address is hard coded to 0. Modify the `ImemStartAddr` parameter in
`./dv/verilator/otbn_top_sim.sv` to change this. Combined with the build script
described above, a single assembly file can be built and run on the simulation as
follows:

```sh
# Create directory for build outputs
mkdir otbn_build
# Build smoke test
hw/ip/otbn/util/build.sh ./hw/ip/otbn/dv/smoke/smoke_test.S ./otbn_build/smoke

# Run the resulting binary on the OTBN standalone simulation
./build/lowrisc_ip_otbn_top_sim_0.1/sim-verilator/Votbn_top_sim -t \
  --meminit=imem,./otbn_build/smoke_imem.elf \
  --meminit=dmem,./otbn_build/smoke_dmem.elf
```

This will initialise the IMem with `./otbn_build/smoke_imem.elf` and the DMem
with `./otbn_build/smoke_dmem.elf`. The `-t` argument enables tracing.  The
simulation automatically halts on an `ecall` instruction and prints the final
register values.

### Run the smoke test

A smoke test which exercises some functionality of OTBN can be found, together
with its expected outputs (in the form of final register values), in
`./hw/ip/otbn/dv/smoke`. The test can be run using a script.

```sh
hw/ip/otbn/dv/smoke/run_smoke.sh
```

This will build the standalone simulation, build the smoke test binary, run it
and check the results are as expected.

### Build the RTL implementation in OT earlgrey simulation

To build the RTL implementation of OTBN in an earlgrey simulation, run `fusesoc`
without passing the `OTBN_MODEL` flag. For example, the Verilator simulation can
be compiled as follows.

```sh
fusesoc --cores-root=. run --target=sim --setup --build lowrisc:systems:top_earlgrey_verilator
```

### Work with the ISA

The instruction set is described in machine readable form in `data/insns.yml`.
This is parsed by Python code in `util/insn_yaml.py`, which runs various sanity
checks on the data. Current tooling that uses this information:

  - `util/yaml_to_doc.py`: Generates a Markdown snippet which is included in
    the OTBN specification.
