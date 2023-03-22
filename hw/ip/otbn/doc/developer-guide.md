# OpenTitan Big Number Accelerator (OTBN)

This directory contains the implementation of the OpenTitan Big Number
Accelerator (OTBN). OTBN is a coprocessor for asymmetric cryptographic
operations like RSA or Elliptic Curve Cryptography (ECC).

See [here](../README.md) for documentation on
the current version of OTBN; documentation matching the code in this directory
can be found in the `doc` directory.

OTBN is under active development. Please ask questions and report issues
through the [GitHub issue tracker](https://github.com/lowRISC/opentitan/issues).

## Develop OTBN

### Build OTBN software

An assembler, linker and disassembler for OTBN can be found in
`hw/ip/otbn/util`. These are wrappers around a RISC-V GCC and binutils toolchain
so one must be available (see the OpenTitan documentation on [obtaining a
toolchain](https://opentitan.org/guides/getting_started#step-3-install-the-lowrisc-risc-v-toolchain).
For more details about the toolchain, see the [user
guide](../../../../doc/contributing/sw/otbn_sw.md)).

`otbn_as.py` and `otbn_ld.py` can be used to build .elf files for use with
simulations. They work work similarly to binutils programs they wrap.

```
hw/ip/otbn/util/otbn_as.py -o prog_bin/prog.o prog.s
hw/ip/otbn/util/otbn_ld.py -o prog_bin/prog.elf prog_bin/prog.o
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

### Run the Python simulator
The quickest way to run an OTBN-only program is to use the Python simulator.
First, generate a `.elf.` file either using the usual build process or by
manually running `otbn_as.py` and `otbn_ld.py` as shown above. Then, from `$REPO_TOP`:
```console
$ hw/ip/otbn/dv/otbnsim/standalone.py -t path/to/prog.elf
```

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

To run several auto-generated binaries against the Verilated RTL, use
the script at `dv/verilator/run-some.py`. For example,

```sh
hw/ip/otbn/dv/verilator/run-some.py --size=1500 --count=50 X
```

will generate and run 50 binaries, each of which will execute up to
1500 instructions when run. The generated binaries, a Verilated model
and the output from running them can all be found in the directory
called `X`.

### Run the smoke test

A smoke test which exercises some functionality of OTBN can be found, together
with its expected outputs (in the form of final register values), in
`./hw/ip/otbn/dv/smoke`. The test can be run using a script.

```sh
hw/ip/otbn/dv/smoke/run_smoke.sh
```

This will build the standalone simulation, build the smoke test binary, run it
and check the results are as expected.

### Run the ISS on its own

There are currently two versions of the ISS and they can be found in
`dv/otbnsim`. The easiest to use is `dv/otbnsim/standalone.py`. This
takes an OTBN binary as an ELF file (as produced by the standard
linker script for `otbn_ld.py`) and can dump the resulting DMEM if given
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
