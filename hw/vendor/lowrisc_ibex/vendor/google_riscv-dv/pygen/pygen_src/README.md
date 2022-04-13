## Overview

RISCV-DV-PyFlow is a purely Python based open-source instruction generator for RISC-V processor
verification. It uses [PyVSC](https://github.com/fvutils/pyvsc) as the main library for
randomization and coverage collection. It currently supports the following features:

- Supported instruction set: RV32IMAFDC, RV64IMAFDC
- Supported privileged modes: For now only machine mode is supported.
- Illegal instruction and HINT instruction generation
- Random forward/backward branch instructions
- Supports mixing directed instructions with random instruction stream
- Support for direct & vectored interrupt table.
- Sub-program generation and random program calls
- Multi-hart support
- Functional coverage framework (reports GUI as well as text, currently
  supports RV32IMFDC extensions)
- Supported ISS : Spike, OVPsim

## Supported tests

- riscv_arithmetic_basic_test
- riscv_amo_test
- riscv_floating_point_arithmetic_test
- riscv_floating_point_rand_test
- riscv_floating_point_mmu_stress_test
- riscv_b_ext_test
- riscv_rand_instr_test
- riscv_jump_stress_test
- riscv_rand_jump_test
- riscv_mmu_stress_test
- riscv_illegal_instr_test
- riscv_unaligned_load_store_test
- riscv_single_hart_test
- riscv_non_compressed_instr_test
- riscv_loop_test


## Getting Started

### Prerequisites

To be able to run the generator, you need to have RISCV-GCC compiler toolchain and ISS
(Instruction Set Simulator) installed (Spike is preferred).


### Install RISCV-DV-PyFlow

Getting the source
```bash
git clone https://github.com/google/riscv-dv.git
```

```bash
pip3 install -r requirements.txt    # install dependencies (only once)
python3 run.py --help
```

## Running the Generator

Command to run a single test:
```bash
python3 run.py --test=riscv_arithmetic_basic_test --simulator=pyflow
```
--simulator=pyflow will invoke the Python generator.

Run a single test 10 times
```bash
python3 run.py --test=riscv_arithmetic_basic_test --iterations=10 --simulator=pyflow
```
Run the generator only, do not compile and simluation with ISS
```bash
python3 run.py --test=riscv_arithmetic_basic_test --simulator=pyflow --steps gen
```
## Coverage Model
The coverage model of PyFlow is developed using PyVSC library.

Command to generate the coverage report.
#### Process spike simulation log and collect functional coverage
```bash
python3 cov.py --dir out/spike_sim/ --simulator=pyflow --enable_visualization
```
--enable_visualization helps enabling coverage report visualization for pyflow.
#### Get the command reference
```bash
cov --help
```
#### Run the coverage flow with predefined targets
```bash
python3 cov.py --dir out/spike_sim/ --simulator=pyflow --enable_visualization --target rv32imc
```
The coverage reports can be viewed using two ways:
1) Text format: By opening the CoverageReport.txt file.
2) GUI format: By opening the cov_db.xml using pyucis-viewer.
The GUI format could be enabled using "--enable_visualization" command option.
```bash
pyucis-viewer cov_db.xml
```
## Note
Currently, time to generate a single program with larger than 10k instructions is around
12 minutes. We are working on improving the overall performance.
