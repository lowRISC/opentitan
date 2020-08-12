## Overview

RISCV-DV is a SV/UVM based open-source instruction generator for RISC-V
processor verification. It currently supports the following features:

- Supported instruction set: RV32IMAFDC, RV64IMAFDC
- Supported privileged mode: machine mode, supervisor mode, user mode
- Page table randomization and exception
- Privileged CSR setup randomization
- Privileged CSR test suite
- Trap/interrupt handling
- Test suite to stress test MMU
- Sub-program generation and random program calls
- Illegal instruction and HINT instruction generation
- Random forward/backward branch instructions
- Supports mixing directed instructions with random instruction stream
- Debug mode support, with fully randomized debug ROM
- Instruction generation coverage model
- Handshake communication with testbench
- Support handcoded assembly test
- Co-simulation with multiple ISS : spike, riscv-ovpsim, whisper, sail-riscv

## Getting Started

### Prerequisites

To be able to run the instruction generator, you need to have an RTL simulator
which supports SystemVerilog and UVM 1.2. This generator has been verified with
Synopsys VCS, Cadence Incisive/Xcelium, Mentor Questa, and Aldec Riviera-PRO simulators.
Please make sure the EDA tool environment is properly setup before running the generator.

### Install RISCV-DV

Getting the source
```bash
git clone https://github.com/google/riscv-dv.git
```

There are two ways that you can run scripts from riscv-dv.

For developers which may work on multiple clones in parallel, using directly run
by `python3` script is highly recommended. Example:

```bash
pip3 install -r requirements.txt    # install dependencies (only once)
python3 run.py --help
```
For normal users, using the python package is recommended. First, cd to the directory
where riscv-dv is cloned and run:

```bash
export PATH=$HOME/.local/bin/:$PATH  # add ~/.local/bin to the $PATH (only once)
pip3 install --user -e .
```

This installs riscv-dv in a mode where any changes within the repo are immediately
available simply by running `run`/`cov`. There is no need to repeatedly run `pip install .`
after each change. Example for running:

```bash
run --help
cov --help
```

Use below command to install Verible, which is the tool to check Verilog style
```bash
verilog_style/build-verible.sh
```

This is the command to run Verilog style check. It's recommended to run and clean up
all the style violations before submit a PR
```bash
verilog_style/run.sh
```

## Document

To understand how to setup and customize the generator, please check the full
document under docs directory. You can use the makefile to generate the
document. [HTML
preview](https://htmlpreview.github.io/?https://github.com/google/riscv-dv/blob/master/docs/build/singlehtml/index.html#document-index).
You can find the prebuilt document under docs/build/singlehtml/index.html

## External contributions and collaborations

RISC-V DV is now contributed to CHIPS Alliance. We have regular meetings to
discuss the issues, feature priorities, development progress etc. Please join
the [mail group](https://lists.chipsalliance.org/g/riscv-dv-wg) for latest
status. 

Please refer to CONTRIBUTING.md for license related questions.

## Supporting model

Please file an issue under this repository for any bug report / integration
issue / feature request. We are looking forward to knowing your experience of
using this flow and how we can make it better together.

## Disclaimer

This is not an officially supported Google product.
