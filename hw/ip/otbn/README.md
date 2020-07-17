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

### Build the RTL implementation

To build the RTL implementation of OTBN in a simulation, run `fusesoc` without
passing the `OTBN_MODEL` flag. For example, the Verilator simulation can be
compiled as follows.

```sh
fusesoc --cores-root=. run --target=sim --setup --build lowrisc:systems:top_earlgrey_verilator
```

### Work with the ISA

The instruction set is described in machine readable form in `data/insns.yml`.
This is parsed by Python code in `util/insn_yaml.py`, which runs various sanity
checks on the data. Current tooling that uses this information:

  - `util/yaml_to_doc.py`: Generates a Markdown snippet which is included in
    the OTBN specification.

### Run the OTBN hello world application

```sh
# Build the software
ninja -C build-out/

# Run the Verilator-based simulation
./build/lowrisc_systems_top_earlgrey_verilator_0.1/sim-verilator/Vtop_earlgrey_verilator \
  --meminit=rom,build-bin/sw/device/boot_rom/boot_rom_sim_verilator.elf \
  --meminit=flash,build-bin/sw/device/examples/hello_otbn/hello_otbn_sim_verilator.elf
```

The `hello_otbn` application writes diagnostic information to the UART, read it
in simulation with e.g. `cat /dev/pts/10`; use the UART device shown when
running the simulation.

### Update the OTBN model (the instruction-set simulator, ISS)

The OTBN model is an instruction set simulator written in Python. It lives
in the `opentitan` repository in the `util/otbnsim` directory, but builds on top
of the `riscv-model` Python package. The code for this package can be found at
https://github.com/wallento/riscv-python-model.

To update the model to the latest recommended version run `pip`.

```sh
# Ensure you have the latest Python dependencies installed
pip3 install --user -U python-requirements.txt
```

### Build the model

In simulation, OTBN can either be built with the "real" RTL implementation, or
with a timing-accurate behavioral model. The `OTBN_MODEL` define can switch
between the two variants, which is accessible in FuseSoC via the `--OTBN_MODEL`
flag.

```sh
# Build the simulation with the --OTBN_MODEL flag
fusesoc --cores-root=. run --target=sim --setup --build lowrisc:systems:top_earlgrey_verilator --OTBN_MODEL
```

### Run only the model

The OTBN model is a standalone Python application.

```sh
otbn-python-model
```
