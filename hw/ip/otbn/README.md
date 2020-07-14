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

## Build the RTL implementation

To build the RTL implementation of OTBN in a simulation, run `fusesoc` without
passing the `OTBN_MODEL` flag. For example, the Verilator simulation can be
compiled as follows.

```sh
fusesoc --cores-root=. run --target=sim --setup --build lowrisc:systems:top_earlgrey_verilator
```
