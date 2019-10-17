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
- Support sub-programs and random program calls
- Support illegal instruction and HINT instruction
- Random forward/backward branch instructions
- Supports mixing directed instructions with random instruction stream
- Debug mode support, with fully randomized debug ROM
- Instruction generation coverage model
- Communication of information to any integrated SV testbench
- Supports co-simulation with multiple ISS : spike, riscv-ovpsim

A CSR test generation script written in Python is also provided, to generate a
directed test suite that stresses all CSR instructions on all of the CSRs that
the core implements.

## Getting Started

### Prerequisites

To be able to run the instruction generator, you need to have an RTL simulator
which supports SystemVerilog and UVM 1.2. This generator has been verified with
Synopsys VCS, Cadence Incisive/Xcelium, and Mentor Questa simulators. Please
make sure the EDA tool environment is properly setup before running the generator.

To be able to run the CSR generation script, the open-source `bitstring`
Python library is required ([bitstring](https://github.com/scott-griffiths/bitstring)).
To install this library, either clone the repository and run the `setup.py`
setup script, or run only one of the below commands:
```
1) sudo apt-get install python3-bitstring (or your OS-specific package manager)
2) pip install bitstring
```

### Running the generator


A simple script "run.py" is provided for you to run a single test or a regression.

You can use --help to get the complete command reference:

```
python3 run.py --help
```

Here is the command to run a single test:

```
python3 run.py --test=riscv_arithmetic_basic_test
```
You can specify the simulator by "-simulator" option

```
python3 run.py --test riscv_arithmetic_basic_test --simulator ius
python3 run.py --test riscv_arithmetic_basic_test --simulator vcs
python3 run.py --test riscv_arithmetic_basic_test --simulator questa
python3 run.py --test riscv_arithmetic_basic_test --simulator dsim
```
The complete test list can be found in [yaml/testlist.yaml](https://github.com/google/riscv-dv/blob/master/yaml/testlist.yaml). To run a full
regression, simply use below command

```
python3 run.py
```

You can also run multiple generator jobs in parallel through LSF

```
python3 run.py --lsf_cmd="bsub -Is"
```

Here's a few more examples of the run command:

```
// Run a single test 10 times
python3 run.py --test riscv_arithmetic_basic_test --iterations 10

// Run a test with verbose logging
python3 run.py --test riscv_arithmetic_basic_test --verbose

// Run a test with a specified seed
python3 run.py --test riscv_arithmetic_basic_test --seed 123

// Skip the generation, run ISS simulation with previously generated program
python3 run.py --test riscv_arithmetic_basic_test --steps iss_sim

// Run the generator only, do not compile and simluation with ISS
python3 run.py --test riscv_arithmetic_basic_test --steps gen

// Compile the generator only, do not simulate
python3 run.py --test riscv_arithmetic_basic_test --co

....
```

### Privileged CSR Test Generation

The CSR generation script is located at
[scripts/gen_csr_test.py](https://github.com/google/riscv-dv/blob/master/scripts/gen_csr_test.py).
The CSR test code that this script generates will execute every CSR instruction
on every processor implemented CSR, writing values to the CSR and then using a
prediction function to calculate a reference value that will be written into
another GPR. The reference value will then be compared to the value actually
stored in the CSR to determine whether to jump to the failure condition or
continue executing, allowing it to be completely self checking. This script has
been integrated with run.py. If you want to run it separately, you can get the
command reference with --help:

```
python3 scripts/gen_csr_test.py --help
```

## Configuration

### Setup regression test list

[Test list in YAML format](https://github.com/google/riscv-dv/blob/master/yaml/testlist.yaml)

```
# test            : Assembly test name
# description     : Description of this test
# gen_opts        : Instruction generator options
# iterations      : Number of iterations of this test
# no_iss          : Enable/disable ISS simulation (Optional)
# gen_test        : Test name used by the instruction generator
# rtl_test        : RTL simulation test name
# cmp_opts        : Compile options passed to the instruction generator
# sim_opts        : Simulation options passed to the instruction generator
# no_post_compare : Enable/disable log comparison (Optional)
# compare_opts    : Options for the RTL & ISS trace comparison

- test: riscv_arithmetic_basic_test
  description: >
    Arithmetic instruction test, no load/store/branch instructions
  gen_opts: >
    +instr_cnt=10000
    +num_of_sub_program=0
    +no_fence=1
    +no_data_page=1'b1
    +no_branch_jump=1'b1
    +boot_mode=m
  iterations: 2
  gen_test: riscv_instr_base_test
  rtl_test: core_base_test

```

Note: To automatically generate CSR tests without having to explicitly run the
script, include `riscv_csr_test` in the testlist as shown in the example YAML
file above.


### Configure the generator to match your processor features

The default configuration of the instruction generator is for RV64IMC RISC-V
processors with address translation capability. You might want to configure the
generator according the feature of your processor.

The static setting of the processor src/riscv_core_setting.sv

```
// Bit width of RISC-V GPR
parameter int XLEN = 64;

// Parameter for SATP mode, set to BARE if address translation is not supported
parameter satp_mode_t SATP_MODE = SV39;

// Supported Privileged mode
privileged_mode_t supported_privileged_mode[] = {USER_MODE,
                                                 SUPERVISOR_MODE,
                                                 MACHINE_MODE};

// Unsupported instructions
riscv_instr_name_t unsupported_instr[] = {};

// ISA supported by the processor
riscv_instr_group_t supported_isa[] = {RV32I, RV32M, RV64I, RV64M};

...
```

### Setup the memory map

Here's a few cases that you might want to allocate the instruction and data
sections to match the actual memory map
- The processor has internal memories, and you want to test load/store from
  various internal/externel memory regions
- The processor implments the PMP feature, and you want to configure the memory
  map to match PMP setting.
- Virtual address translation is implmented and you want to test load/store from
  sparse memory locations to verify data TLB replacement logic.

You can configure the memory map in [riscv_instr_gen_config.sv](https://github.com/google/riscv-dv/blob/master/src/riscv_instr_gen_config.sv)

```
  mem_region_t mem_region[$] = '{
    '{name:"region_0", size_in_bytes: 4096,      xwr: 3'b111},
    '{name:"region_1", size_in_bytes: 4096 * 4,  xwr: 3'b111},
    '{name:"region_2", size_in_bytes: 4096 * 2,  xwr: 3'b111},
    '{name:"region_3", size_in_bytes: 512,       xwr: 3'b111},
    '{name:"region_4", size_in_bytes: 4096,      xwr: 3'b111}
  };
```

Each memory region belongs to a separate section in the generated assembly
program. You can modify the link script to link each section to the target
memory location. Please avoid setting a large memory range as it could takes a
long time to randomly initializing the memory. You can break down a large memory
region to a few representative small regions which covers all the boundary
conditions for the load/store testing.


### Runtime options of the generator

| Option                      | Description                                       | Default |
|:---------------------------:|:-------------------------------------------------:|:-------:|
| num_of_tests                | Number of assembly tests to be generated          | 1       |
| num_of_sub_program          | Number of sub-program in one test                 | 5       |
| instr_cnt                   | Instruction count per test                        | 200     |
| enable_page_table_exception | Enable page table exception                       | 0       |
| enable_unaligned_load_store | Enable unaligned memory operations                | 0       |
| no_ebreak                   | Disable ebreak instruction                        | 1       |
| no_wfi                      | Disable WFI instruction                           | 1       |
| no_dret                     | Disable dret instruction                          | 1       |
| no_branch_jump              | Disable branch/jump instruction                   | 0       |
| no_load_store               | Disable load/store instruction                    | 0       |
| no_csr_instr                | Disable CSR instruction                           | 0       |
| no_fence                    | Disable fence instruction                         | 0       |
| illegal_instr_ratio         | Number of illegal instructions every 1000 instr   | 0       |
| hint_instr_ratio            | Number of HINT instructions every 1000 instr      | 0       |
| boot_mode                   | m:Machine mode, s:Supervisor mode, u:User mode    | m       |
| no_directed_instr           | Disable directed instruction stream               | 0       |
| require_signature_addr      | Set to 1 if test needs to talk to testbench       | 0       |
| signature_addr              | Write to this addr to send data to testbench      | 0       |
| enable_interrupt            | Enable MStatus.MIE, used in interrupt test        | 0       |
| gen_debug_section           | Disables randomized debug_rom section             | 0       |
| num_debug_sub_program       | Number of debug sub-programs in test              | 0       |
| enable_ebreak_in_debug_rom  | Generate ebreak instructions inside debug ROM     | 0       |
| set_dcsr_ebreak             | Randomly enable dcsr.ebreak(m/s/u)                | 0       |
| randomize_csr               | Fully randomize main CSRs (xSTATUS, xIE)          | 0       |


### Setup Privileged CSR description

This YAML description file of all CSRs is only required for the privileged CSR
test. All other standard tests do not use this description.

[CSR descriptions in YAML
format](https://github.com/google/riscv-dv/blob/master/yaml/csr_template.yaml)

```
- csr: CSR_NAME
  description: >
    BRIEF_DESCRIPTION
  address: 0x###
  privilege_mode: MODE (D/M/S/H/U)
  rv32:
    - MSB_FIELD_NAME:
      - description: >
          BRIEF_DESCRIPTION
      - type: TYPE (WPRI/WLRL/WARL/R)
      - reset_val: RESET_VAL
      - msb: MSB_POS
      - lsb: LSB_POS
    - ...
    - ...
    - LSB_FIELD_NAME:
      - description: ...
      - type: ...
      - ...
  rv64:
    - MSB_FIELD_NAME:
      - description: >
          BRIEF_DESCRIPTION
      - type: TYPE (WPRI/WLRL/WARL/R)
      - reset_val: RESET_VAL
      - msb: MSB_POS
      - lsb: LSB_POS
    - ...
    - ...
    - LSB_FIELD_NAME:
      - description: ...
      - type: ...
      - ...
```

To specify what ISA width should be generated in the test, simply include the
matching rv32/rv64/rv128 entry and fill in the appropriate CSR field entries.


### Adding new instruction stream and test

Please refer to src/src/riscv_load_store_instr_lib.sv for an example on how to
add a new instruction stream.
After the new instruction stream is created, you can use a runtime option to mix
it with random instructions

```
//+directed_instr_n=instr_sequence_name,frequency(number of insertions per 1000 instructions)
+directed_instr_5=riscv_multi_page_load_store_instr_stream,4
```

## Compile generated programs with GCC

- Install [riscv-gcc](https://github.com/riscv/riscv-gcc) toolchain
- Set environment variable RISCV_GCC to the RISC-V gcc executable
  executable. (example: <install_dir>/bin/riscv32-unknown-elf-gcc)
- Set environment variable RISCV_OBJCOPY to RISC-v objcopy executable
  executable. (example: <install_dir>/bin/riscv32-unknown-elf-objcopy)

## Run ISS (Instruction Set Simulator) simulation

Currently three ISS are supported, the default ISS is spike. You can install any
one of below to run ISS simulation.

- [spike](https://github.com/riscv/riscv-isa-sim#) setup
  - Follow the [steps](https://github.com/riscv/riscv-isa-sim#build-steps) to build spike
  - Install spike with "--enable-commitlog"
  - Set environment variable SPIKE_PATH to the directory of the spike binary
- [riscv-ovpsim](https://github.com/riscv/riscv-ovpsim) setup
  - Download the riscv-ovpsim binary
  - Set environment variable OVPSIM_PATH to the directory of the ovpsim binary
- [sail-riscv](https://github.com/rems-project/sail-riscv) setup
  - Follow the [steps](https://github.com/rems-project/sail-riscv/blob/master/README.md) to install sail-riscv
  - Set environment variable SAIL_RISCV to the sail-riscv binary

You can use -iss to run with different ISS.

```
// Run ISS with spike
python3 run.py --test riscv_arithmetic_basic_test --iss spike

// Run ISS with riscv-ovpsim
python3 run.py --test riscv_rand_instr_test --iss ovpsim

// Run ISS with sail-riscv
python3 run.py --test riscv_rand_instr_test --iss sail
```

To run with ISS simulation for RV32IMC, you can specify ISA and ABI from command
line like this:

```
// Run a full regression with RV32IMC
python3 run.py --isa rv32imc --mabi ilp32
```

We have added a flow to run ISS simulation with both spike and riscv-ovpsim,
the instruction trace from these runs will be cross compared. This could greatly
speed up your development of new test without the need to simulate against a
real RISC-V processor.

```
python3 run.py --test=riscv_rand_instr_test --iss=spike,ovpsim
python3 run.py --test=riscv_rand_instr_test --iss=spike,sail
```

### Integrate a new ISS

You can add a new entry in [iss.yaml](https://github.com/google/riscv-dv/blob/master/yaml/iss.yaml)

```
- iss: new_iss_name
  path_var: ISS_PATH
  cmd: >
    <path_var>/iss_executable --isa=<variant> -l <elf>
```

Simulate with the new ISS

```
python3 run.py --test riscv_arithmetic_basic_test --iss new_iss_name
```

## End-to-end RTL and ISS co-simulation flow

We have collaborated with LowRISC to apply this flow for [IBEX RISC-V core
verification](https://github.com/lowRISC/ibex/blob/master/doc/verification.rst). You can use
it as a reference to setup end-to-end co-simulation flow.
This repo is still under active development, here's recommended approach to
customize the instruction generator while keeping the minimum effort of merging
upstream changes.
- Do not modify the upstream classes directly. When possible, extend from
  the upstream classses and implement your own functionalities.
- Add your extensions under user_extension directory, and add the files to
  user_extension/user_extension.svh. If you prefer to put your extensions in a
  different directory, you can use "-ext <user_extension_path>" to override the
  user extension path.
- Create a new file for riscv_core_setting.sv, add the path with below option:
  "-cs <new_core_setting_path>"
- Use command line type override to use your extended classes.
  --sim_opts="+uvm_set_type_override=<upstream_class>,<extended_class>"

You can refer to [riscv-dv extension for ibex](https://github.com/lowRISC/ibex/blob/master/dv/uvm/Makefile#L68) for a working example.

We have plan to open-source the end-to-end environment of other advanced RISC-V
processors. Stay tuned!

## Functional coverage (work in progress)

This flow extracts funcitonal coverage information from the
instruction trace generated by ISS. It's indepdent of the instruction generation
flow and does not require a tracer implmentation in the RTL. You can use this
flow as long as your program can be run with the ISS supported in this flow. The
flow parses the instruction trace log and converts it to a CSV trace format. After
that, a SV test will be run to process the CSV trace files and sample functional
coverage from there.

The functional covergroup is defined in [riscv_instr_cover_group.sv](https://github.com/google/riscv-dv/blob/master/src/riscv_instr_cover_group.sv). It includes below major categories:
- Cover all operands for each instruction
- Hazard conditions
- Corner cases like overflow, underflow, divide by zero
- Aligned/unaligned load/store
- Positive/negative immediate value
- Forward/backward branches, branch hit history
- Hint instruction
- Illegal instruction
- All compressed and non-compressed opcode
- Access to all implemened privieleged CSR
- Exception and interrupt

The functional covergroup is still under active development. Please feel free to
add anything you are interested or file a bug for any feature request. 

Before start, please check the you have modified [riscv_core_setting.sv](https://github.com/google/riscv-dv/blob/master/setting/riscv_core_setting.sv) to reflect your processor capabilities. The covergroup is selectively instantiated based on this setting so that you don't need to deal with excluding unrelated coverpoint later. You also need to get spike ISS setup before running this flow.


```
// Process spike simulation log and collect functional coverage
python3 cov.py --dir out/spike_sim

// Get the command reference
python3 cov.py --help
```

The coverage sampling from the CSV could be time consuming if you have a large
number of log to process. You can split them to small batches and run with LSF
in parallel.

```
// Split the run to process 5 CSV at a time, and run with LSF
python3 cov.py --dir out/spike_sim --lsf_cmd "bsub ....." -bz 5
```

There is also a debug mode which allow you randomize the instruction and sample
coverage directly. This is only used to test the new functional coverage
implmentation.

```
// Randomly generate 100000 instructions, split to 20000 instructions per batch
python3 cov.py -d -i 100000 -bz 20000
```


## Supporting model

Please file an issue under this repository for any bug report / integration
issue / feature request. We are looking forward to knowing your experience of
using this flow and how we can make it better together.

## External contributions

We definitely welcome external contributions. We hope it could be a
collaborative effort to build a strong open source RISC-V processor
verification platform. Free feel to submit your pull request for review.
Please refer to CONTRIBUTING.md for license related questions.

## Disclaimer

This is not an officially supported Google product.
