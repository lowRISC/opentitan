Configuration
=============

Configure the generator to match your processor features
--------------------------------------------------------

The default configuration of the instruction generator is **RV32IMC** (machine
mode only). A few pre-defined configurations can be found under "target" directory,
you can run with these targets if it matches your processor specificationi::

    run                   # Default target rv32imc
    run --target rv32i    # rv32i, machine mode only
    run --target rv32imc  # rv32imc, machine mode only
    run --target rv64imc  # rv64imc, machine mode only
    run --target rv64gc   # rv64gc, SV39, M/S/U mode

If you want to have a custom setting for your processor, you can make a copy of
existing target directory as the template, and modify riscv_core_setting.sv to
match your processor capability.

.. code-block:: verilog

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

You can then run the generator with ``--custom_target <target_dir>``::

    # You need to manually specify isa and mabi for your custom target
    run --custom_target <target_dir> --isa <isa> --mabi <mabi>
    ...

Setup the memory map
--------------------

Here's a few cases that you might want to allocate the instruction and data
sections to match the actual memory map

1.  The processor has internal memories, and you want to test load/store from
    various internal/externel memory regions
2.  The processor implments the PMP feature, and you want to configure the memory
    map to match PMP setting.
3.  Virtual address translation is implmented and you want to test load/store from
    sparse memory locations to verify data TLB replacement logic.

You can configure the memory map in `riscv_instr_gen_config.sv`_::

    mem_region_t mem_region[$] = '{
        '{name:"region_0", size_in_bytes: 4096,      xwr: 3'b111},
        '{name:"region_1", size_in_bytes: 4096 * 4,  xwr: 3'b111},
        '{name:"region_2", size_in_bytes: 4096 * 2,  xwr: 3'b111},
        '{name:"region_3", size_in_bytes: 512,       xwr: 3'b111},
        '{name:"region_4", size_in_bytes: 4096,      xwr: 3'b111}
    };

Each memory region belongs to a separate section in the generated assembly
program. You can modify the link script to link each section to the target
memory location. Please avoid setting a large memory range as it could takes a
long time to randomly initializing the memory. You can break down a large memory
region to a few representative small regions which covers all the boundary
conditions for the load/store testing.

.. _riscv_instr_gen_config.sv: https://github.com/google/riscv-dv/blob/master/src/riscv_instr_gen_config.sv

Setup regression test list
--------------------------

Test list in `YAML format`_

.. code-block:: yaml

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

.. _YAML format: https://github.com/google/riscv-dv/blob/master/yaml/base_testlist.yaml

You can also add directed assembly/C test in the testlist

.. code-block:: yaml

    - test: riscv_single_c_test
      description: >
         single c test entry
      iterations: 1
      c_test: sample_c.c

    - test: riscv_c_regression_test
      description: >
        Run all c tests under the given directory
      iterations: 1
      c_test: c_test_directory
      gcc_opts:
         # Some custom gcc options

    - test: riscv_single_asm_test
      description: >
         single assembly test entry
      iterations: 1
      asm_test: sample_asm.S

    - test: riscv_asm_regression_test
      description: >
        Run all assembly tests under the given directory
      iterations: 1
      asm_test: assembly_test_directory
      gcc_opts:
         # Some custom gcc options


Runtime options of the generator
--------------------------------
+---------------------------------+---------------------------------------------------+---------+
| Option                          | Description                                       | Default |
+=================================+===================================================+=========+
| num_of_tests                    | Number of assembly tests to be generated          | 1       |
+---------------------------------+---------------------------------------------------+---------+
| num_of_sub_program              | Number of sub-program in one test                 | 5       |
+---------------------------------+---------------------------------------------------+---------+
| instr_cnt                       | Instruction count per test                        | 200     |
+---------------------------------+---------------------------------------------------+---------+
| enable_page_table_exception     | Enable page table exception                       | 0       |
+---------------------------------+---------------------------------------------------+---------+
| enable_unaligned_load_store     | Enable unaligned memory operations                | 0       |
+---------------------------------+---------------------------------------------------+---------+
| no_ebreak                       | Disable ebreak instruction                        | 1       |
+---------------------------------+---------------------------------------------------+---------+
| no_wfi                          | Disable WFI instruction                           | 1       |
+---------------------------------+---------------------------------------------------+---------+
| set_mstatus_tw                  | Enable WFI to be treated as illegal instruction   | 0       |
+---------------------------------+---------------------------------------------------+---------+
| no_dret                         | Disable dret instruction                          | 1       |
+---------------------------------+---------------------------------------------------+---------+
| no_branch_jump                  | Disable branch/jump instruction                   | 0       |
+---------------------------------+---------------------------------------------------+---------+
| no_csr_instr                    | Disable CSR instruction                           | 0       |
+---------------------------------+---------------------------------------------------+---------+
| enable_illegal_csr_instruction  | Enable illegal CSR instructions                   | 0       |
+---------------------------------+---------------------------------------------------+---------+
| enable_access_invalid_csr_level | Enable accesses to higher privileged CSRs         | 0       |
+---------------------------------+---------------------------------------------------+---------+
| enable_dummy_csr_write          | Enable some dummy CSR writes in setup routine     | 0       |
+---------------------------------+---------------------------------------------------+---------+
| enable_misaligned_instr         | Enable jumps to misaligned instruction addresses  | 0       |
+---------------------------------+---------------------------------------------------+---------+
| no_fence                        | Disable fence instruction                         | 0       |
+---------------------------------+---------------------------------------------------+---------+
| no_data_page                    | Disable data page generation                      | 0       |
+---------------------------------+---------------------------------------------------+---------+
| disable_compressed_instr        | Disable compressed instruction generation         | 0       |
+---------------------------------+---------------------------------------------------+---------+
| illegal_instr_ratio             | Number of illegal instructions every 1000 instr   | 0       |
+---------------------------------+---------------------------------------------------+---------+
| hint_instr_ratio                | Number of HINT instructions every 1000 instr      | 0       |
+---------------------------------+---------------------------------------------------+---------+
| boot_mode                       | m:Machine mode, s:Supervisor mode, u:User mode    | m       |
+---------------------------------+---------------------------------------------------+---------+
| no_directed_instr               | Disable directed instruction stream               | 0       |
+---------------------------------+---------------------------------------------------+---------+
| require_signature_addr          | Set to 1 if test needs to talk to testbench       | 0       |
+---------------------------------+---------------------------------------------------+---------+
| signature_addr                  | Write to this addr to send data to testbench      | 0       |
+---------------------------------+---------------------------------------------------+---------+
| enable_interrupt                | Enable MStatus.MIE, used in interrupt test        | 0       |
+---------------------------------+---------------------------------------------------+---------+
| enable_timer_irq                | Enable xIE.xTIE, used to enable timer interrupts  | 0       |
+---------------------------------+---------------------------------------------------+---------+
| gen_debug_section               | Enables randomized debug_rom section              | 0       |
+---------------------------------+---------------------------------------------------+---------+
| num_debug_sub_program           | Number of debug sub-programs in test              | 0       |
+---------------------------------+---------------------------------------------------+---------+
| enable_ebreak_in_debug_rom      | Generate ebreak instructions inside debug ROM     | 0       |
+---------------------------------+---------------------------------------------------+---------+
| set_dcsr_ebreak                 | Randomly enable dcsr.ebreak(m/s/u)                | 0       |
+---------------------------------+---------------------------------------------------+---------+
| enable_debug_single_step        | Enable debug single stepping functionality        | 0       |
+---------------------------------+---------------------------------------------------+---------+
| randomize_csr                   | Fully randomize main CSRs (xSTATUS, xIE)          | 0       |
+---------------------------------+---------------------------------------------------+---------+

Setup Privileged CSR description (optional)
-------------------------------------------

This YAML description file of all CSRs is only required for the privileged CSR
test. All other standard tests do not use this description.

`CSR descriptions in YAML format`_

.. code-block:: yaml

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

.. _CSR descriptions in YAML format: https://github.com/google/riscv-dv/blob/master/yaml/csr_template.yaml

To specify what ISA width should be generated in the test, simply include the
matching rv32/rv64/rv128 entry and fill in the appropriate CSR field entries.

Privileged CSR Test Generation (optional)
-----------------------------------------

The CSR generation script is located at `scripts/gen_csr_test.py`_.
The CSR test code that this script generates will execute every CSR instruction
on every processor implemented CSR, writing values to the CSR and then using a
prediction function to calculate a reference value that will be written into
another GPR. The reference value will then be compared to the value actually
stored in the CSR to determine whether to jump to the failure condition or
continue executing, allowing it to be completely self checking. This script has
been integrated with run.py. If you want to run it separately, you can get the
command reference with --help::

    python3 scripts/gen_csr_test.py --help

.. _scripts/gen_csr_test.py: https://github.com/google/riscv-dv/blob/master/scripts/gen_csr_test.py

Adding new instruction stream and test
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Please refer to src/src/riscv_load_store_instr_lib.sv for an example on how to
add a new instruction stream.
After the new instruction stream is created, you can use a runtime option to mix
it with random instructions::


    //+directed_instr_n=instr_sequence_name,frequency(number of insertions per 1000 instructions)
    +directed_instr_5=riscv_multi_page_load_store_instr_stream,4

    // An alternative command line options for directed instruction stream
    +stream_name_0=riscv_multi_page_load_store_instr_stream
    +stream_freq_0=4

Integrate a new ISS
~~~~~~~~~~~~~~~~~~~

You can add a new entry in `iss.yaml`_::

    - iss: new_iss_name
      path_var: ISS_PATH
      cmd: >
        <path_var>/iss_executable --isa=<variant> -l <elf>

Simulate with the new ISS::

    run --test riscv_arithmetic_basic_test --iss new_iss_name

.. _iss.yaml: https://github.com/google/riscv-dv/blob/master/yaml/iss.yaml
