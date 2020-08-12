### Overview

This directory contains the proof-of-concept work of python based RISC-V random
instruction generator. The class structure can be directly mapped to the
existing SV/UVM verison. The constraint part is implemented based on
[python-constraint](https://labix.org/python-constraint).

The work here is just experimental. We plan to take a fresh look of the
framework and build a scalable python based generator in the near future.

### Install required packages

```bash
pip3 install python-constraint
pip3 install numpy
pip3 install bitstring
```

### Generate a simple test

```bash
python3 riscv_asm_program_gen.py
```
