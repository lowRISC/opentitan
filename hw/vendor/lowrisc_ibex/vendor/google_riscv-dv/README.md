# RISCV-DV

RISCV-DV is a SV/UVM based open-source instruction generator for RISC-V
processor verification. It currently supports the following features:

- Supported instruction set: RV32IMC, RV64IMC
- Supported privileged mode: machine mode, supervisor mode, user mode
- Page table randomization and exception
- Privileged CSR setup randomization
- Trap/interrupt handling
- Test suite to stress test MMU
- Support sub-programs and random program calls
- Support illegal instruction and HINT instruction
- Random forward/backward branch instructions
- Supports mixing directed instructions with random instruction stream
- Supports co-simulation with multiple ISS : spike, riscv-ovpsim

## Getting Started

### Prerequisites

To be able to run the instruction generator, you need to have an RTL simulator
which supports SystemVerilog and UVM 1.2. This generator has been verified with
Synopsys VCS, Cadence Incisive/Xcelium, and Mentor Questa simulators. Please
make sure the EDA tool environment is properly setup before running the generator.

### Running the generator

A simple script "run" is provided for you to run a single test or a regression.
Here is the command to run a single test:

```
python3 run.py --test=riscv_arithmetic_basic_test
```
You can specify the simulator by "-simulator" option

```
python3 run.py --test=riscv_arithmetic_basic_test --simulator=irun
python3 run.py --test=riscv_arithmetic_basic_test --simulator=vcs
python3 run.py --test=riscv_arithmetic_basic_test --simulator=questa
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
// Get the complete command reference info
python3 run.py --help

// Run a single test 10 times
python3 run.py --test=riscv_page_table_exception_test --iterations=10

// Run a test with a specified seed
python3 run.py --test=riscv_page_table_exception_test --seed=123

// Skip the generation, run ISS simulation with previously generated program
python3 run.py --test=riscv_page_table_exception_test --steps=iss_sim
....
```

## Configuration

### Setup regression test list

[Test list in YAML format](https://github.com/google/riscv-dv/blob/master/yaml/testlist.yaml)

```
# test         : Assembly test name
# description  : Description of this test
# gen_opts     : Instruction generator options
# iterations   : Number of iterations of this test
# gen_test     : Test name used by the instruction generator
# rtl_test     : RTL simulation test name
# cmp_opts     : Compile options passed to the instruction generator
# sim_opts     : Simulation options passed to the instruction generator
# compare_opts : Options for the RTL & ISS trace comparison

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

### Runtime options of the generator

| Option   |      Description      | default |
|----------|:-------------:|:------:|
| num_of_tests |  Number of assembly tests to be generated | 1 |
| num_of_sub_program |    Number of sub-program in one test    | 5 |
| instr_cnt | Instruction count per test  | 200 | 
| enable_page_table_exception | Enable page table exception  | 0 |
| no_ebreak |  Disable ebreak instruction  | 1 |
| no_wfi | Disable WFI instruction  | 1 |
| no_branch_jump | Disable branch/jump instruction   | 0 |
| no_load_store | Disable load/store instruction  | 0 |
| no_csr_instr | Disable CSR instruction | 0 |
| no_fence | Disable fence instruction  | 0 |
| enable_illegal_instruction | Enable illegal instructions  | 0 |
| enable_hint_instruction |  Enable HINT instruction  | 0 |
| boot_mode | m:Machine mode, s:Supervisor mode, u:User mode  | m |
| no_directed_instr | Disable directed instruction stream  | 0 |
| enable_interrupt | Enable MStatus.MIE, used in interrupt test | 0 |

### Adding new instruction stream and test

Please refer to src/src/riscv_load_store_instr_lib.sv for an example on how to
add a new instruction stream.
After the new instruction stream is created, you can use a runtime option to mix
it with random instructions

```
//+directed_instr_n=instr_sequence_name,frequency(number of insertions per 1000 instructions)
+directed_instr_5=riscv_multi_page_load_store_instr_stream,4
```

## Run ISS(Instruction Set Simulator) simulation

The default ISS is spike. Thanks for the great support from Imperas Software Ltd.,
we have added the support for [riscv-ovpsim](https://github.com/riscv/riscv-ovpsim).

- spike setup
  - Follow the [steps](https://github.com/riscv/riscv-isa-sim#build-steps) to build spike
     - Make sure RISCV_ENABLE_COMMITLOG is defined in [config.h.in](https://github.com/riscv/riscv-isa-sim/blob/master/config.h.in)
  - Set environment variable SPIKE_PATH to the directory of the spike binary
- [riscv-ovpsim](https://github.com/riscv/riscv-ovpsim) setup
  - Download the riscv-ovpsim binary
  - Set environment variable OVPSIM_PATH to the directory of the ovpsim binary


You can use -iss to run with different ISS.

```
// Run ISS with spike
python3 run.py --test=riscv_page_table_exception_test --iss=spike

// Run ISS with riscv-ovpsim
python3 run.py --test=riscv_rand_instr_test --iss=ovpsim
```

To run with ISS simulation for RV32IMC, you can specify ISA and ABI from command
line like this:

```
// Run a full regression with RV32IMC
python3 run.py --isa=rv32imc --mabi=ilp32
```

We have added a flow to run ISS simulation with both spike and riscv-ovpsim,
the instruction trace from these runs will be cross compared. This could greatly
speed up your development of new test without the need to simulate against a
real RISC-V processor.

```
python3 run.py --test=riscv_rand_instr_test --iss=spike,ovpsim
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
python3 run.py --test=riscv_page_table_exception_test --iss=new_iss_name
```

## End-to-end RTL and ISS co-simulation flow

We have collaborated with LowRISC to apply this flow for [IBEX RISC-V core
verification](https://github.com/lowRISC/ibex/tree/master/dv/uvm). You can use
it as a reference to setup end-to-end co-simulation flow. It's also a good
reference for [customizing the generator](https://github.com/lowRISC/ibex/tree/master/dv/uvm/riscv_dv_extension) without getting impacted by upstream
changes.
We have plan to open-source the end-to-end environment of other advanced RISC-V
processors. Stay tuned!

## Supporting model

Please file an issue under this repository for any bug report / integration
issue / feature request. We are looking forward to knowing your experience of
using this flow and how we can make it better together.

## External contributions

We definitely welcome external contributions. We hope it could be a
collaborative effort to build a strong open source RISC-V processor
verification platform. Free feel to submit your pull request for review.
Please refer to CONTRIBUTING.md for license related questions.

## Future release plan

We have some work in progress which will be part of future releases:

-   Privileged CSR test suite.
-   Coverage model.
-   Debug mode support

### DEPRECATED simulation flow

Note: The flow mentioned below will soon be deprecated. Please switch to new
flow.

A simple script "run" is provided for you to run a single test or a regression.
Here is the command to run a single test:

```
./run -test riscv_instr_base_test
```
You can specify the simulator by "-tool" option

```
./run -test riscv_instr_base_test -tool irun
./run -test riscv_instr_base_test -tool vcs
./run -test riscv_instr_base_test -tool questa
```
The complete test list can be found in testlist. To run a full regression, you
can just specify the test name to "all".

```
./run -test all
```
The script will run each test in the test list sequentially with the iteration
count specified in the "testlist". All the generated RISC-V assembly will be
listed when the regression is done. If it is successful, you should see the
following output:

```
===========================================================
                Generated RISC-V assembly tests
 ----------------------------------------------------------
./out_2018-11-20/asm_tests/riscv_arithmetic_basic_test.0.S
./out_2018-11-20/asm_tests/riscv_machine_mode_rand_test.0.S
./out_2018-11-20/asm_tests/riscv_mmu_stress_test.0.S
./out_2018-11-20/asm_tests/riscv_mmu_stress_test.1.S
./out_2018-11-20/asm_tests/riscv_no_fence_test.0.S
./out_2018-11-20/asm_tests/riscv_page_table_exception_test.0.S
./out_2018-11-20/asm_tests/riscv_page_table_exception_test.1.S
./out_2018-11-20/asm_tests/riscv_privileged_mode_rand_test.0.S
./out_2018-11-20/asm_tests/riscv_privileged_mode_rand_test.1.S
./out_2018-11-20/asm_tests/riscv_rand_instr_test.0.S
./out_2018-11-20/asm_tests/riscv_rand_instr_test.1.S
./out_2018-11-20/asm_tests/riscv_rand_jump_test.0.S
./out_2018-11-20/asm_tests/riscv_sfence_exception_test.0.S
```

Here's a few more examples of the run command:

```
// Run a single test 10 times
./run -test riscv_page_table_exception_test -n 10

// Run a test with a specified seed
./run -test riscv_page_table_exception_test -seed 123

// Run a test with addtional runtime options, separated with comma
./run -test riscv_rand_instr_test -runo +instr_cnt=10000,+no_fence=1

// Two steps compile and simulation (Avoid multiple compilation)
./run -co # compile only
# Generate multiple tests
./run -so -test riscv_rand_instr_test -n 10
./run -so -test riscv_mmu_stress_test -n 20
....
```
## Disclaimer

This is not an officially supported Google product.
