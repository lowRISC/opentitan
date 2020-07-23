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
`./dv/verilator/otbn_top_sim.sv` to change this. The simulation is run as
follows:

```sh
./build/lowrisc_ip_otbn_top_sim_0.1/sim-verilator/Votbn_top_sim -t \
  --meminit=imem,imem_contents.vmem --meminit=dmem,dmem_contents.vmem
```

This will initialise the IMem with `imem_contents.vmem` and the DMem with
`dmem_contents.vmem`. The `-t` argument enables tracing. The simulation
automatically halts on an `ecall` instruction.

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
