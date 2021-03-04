Getting Started
===============
Prerequisites
-------------

To be able to run the instruction generator, you need to have an RTL simulator
which supports SystemVerilog and UVM 1.2. This generator has been verified with
Synopsys VCS, Cadence Incisive/Xcelium, Mentor Questa, and Aldec Riviera-PRO simulators.
Please make sure the EDA tool environment is properly setup before running the generator.

Install RISCV-DV
----------------

Getting the source

1.  Install `git`_
2.  ``git clone https://github.com/google/riscv-dv.git``
3.  ``cd riscv-dv``

.. _git: https://git-scm.com/

There are two ways that you can run scripts from riscv-dv.

For developers which may work on multiple clones in parallel, using directly run
by `python3` script is highly recommended. Example::

    pip3 install -r requirements.txt     # install dependencies (only once)
    python3 run.py --help

For normal users, using the python package is recommended. First, cd to the directory
where riscv-dv is cloned and run::

    export PATH=$HOME/.local/bin/:$PATH  # add ~/.local/bin to the $PATH (only once)
    pip3 install --user -e .

This installs riscv-dv in a mode where any changes within the repo are immediately
available simply by running `run`/`cov`. There is no need to repeatedly run `pip install .`
after each change. Example for running::

    run --help
    cov --help

Setup RISCV-GCC compiler toolchain
----------------------------------

1.  Install `riscv-gcc`_ toolchain
2.  Set environment variable RISCV_GCC to the RISC-V gcc executable
    executable. (example: <install_dir>/bin/riscv32-unknown-elf-gcc)
3.  Set environment variable RISCV_OBJCOPY to RISC-v objcopy executable
    executable. (example: <install_dir>/bin/riscv32-unknown-elf-objcopy)

.. _riscv-gcc: https://github.com/riscv/riscv-gcc

Sample .bashrc setup::

    export RISCV_TOOLCHAIN=<riscv_gcc_install_path>
    export RISCV_GCC="$RISCV_TOOLCHAIN/bin/riscv32-unknown-elf-gcc"
    export RISCV_OBJCOPY="$RISCV_TOOLCHAIN/bin/riscv32-unknown-elf-objcopy"

Setup ISS (instruction set simulator)
-------------------------------------

Currently three ISS are supported, the default ISS is spike. You can install any
one of below to run ISS simulation.

1.  - `spike`_ setup
    - Follow the instructions to build spike
    - Build spike with "--enable-commitlog"
    - Set environment variable SPIKE_PATH to the directory of the spike binary
2.  - `riscv-ovpsim`_ setup
    - Download the riscv-ovpsim binary
    - Set environment variable OVPSIM_PATH to the directory of the ovpsim binary
3.  - `whisper`_ (swerv-ISS) setup
    - Follow the instruction to install the ISS, and set WHISPER_ISS to the whisper binary
4.  - `sail-riscv`_ setup
    - Follow the `sail-riscv steps`_ to install sail-riscv
    - Set environment variable SAIL_RISCV to the path of sail-riscv binary

.. _spike: https://github.com/riscv/riscv-isa-sim
.. _riscv-ovpsim: https://github.com/riscv/riscv-ovpsim
.. _whisper: https://github.com/westerndigitalcorporation/swerv-ISS
.. _sail-riscv: https://github.com/rems-project/sail-riscv
.. _sail-riscv steps: https://github.com/rems-project/sail-riscv/blob/master/README.md

Sample .bashrc setup::

    export SPIKE_PATH=$RISCV_TOOLCHAIN/bin
    export SAIL_RISCV="xx/xxx/ocaml_emulator"
    export OVPSIM_PATH=/xx/xxx/riscv-ovpsim/bin/Linux64
    export WHISPER_ISS="xx/xxx/swerv-ISS/build-Linux/whisper"

Running the generator
---------------------

A simple script `run.py` is provided for you to run a single test or a regression.

You can use --help to get the complete command reference::

    run --help

Here is the command to run a single test::

    run --test=riscv_arithmetic_basic_test

You can specify the simulator by "-simulator" option::

    run --test riscv_arithmetic_basic_test --simulator ius
    run --test riscv_arithmetic_basic_test --simulator vcs
    run --test riscv_arithmetic_basic_test --simulator questa
    run --test riscv_arithmetic_basic_test --simulator dsim
    run --test riscv_arithmetic_basic_test --simulator qrun
    run --test riscv_arithmetic_basic_test --simulator riviera

The complete test list can be found in `base testlist yaml`_. To run a full regression, simply use below command::

    run

You can also run multiple generator jobs in parallel through LSF::

    run --lsf_cmd="bsub -Is"

Here's a few more examples of the run command::

    # Run a single test 10 times
    run --test riscv_arithmetic_basic_test --iterations 10

    # Run multiple tests
    run --test riscv_arithmetic_basic_test,riscv_rand_instr_test

    # Run a test with verbose logging
    run --test riscv_arithmetic_basic_test --verbose

    # Run a test with a specified seed
    run --test riscv_arithmetic_basic_test --seed 123

    # Skip the generation, run ISS simulation with previously generated program
    run --test riscv_arithmetic_basic_test --steps iss_sim

    # Run the generator only, do not compile and simluation with ISS
    run --test riscv_arithmetic_basic_test --steps gen

    # Compile the generator only, do not simulate
    run --test riscv_arithmetic_basic_test --co

    ....

.. _base testlist yaml: https://github.com/google/riscv-dv/blob/master/yaml/base_testlist.yaml

Run ISS simulation
------------------

You can use -iss to run with different ISS::

    # Run ISS with spike
    run --test riscv_arithmetic_basic_test --iss spike

    # Run ISS with riscv-ovpsim
    run --test riscv_rand_instr_test --iss ovpsim

    # Run ISS with whisper (swerv-ISS)
    run --test riscv_rand_instr_test --iss whisper

    # Run ISS with sail-riscv
    run --test riscv_rand_instr_test --iss sail

To run with ISS simulation for RV32IMC, you can specify ISA and ABI from command
line like this::


    # Run a full regression with RV32IMC
    run --isa rv32imc --mabi ilp32

We have added a flow to run ISS simulation with both spike and riscv-ovpsim,
the instruction trace from these runs will be cross compared. This could greatly
speed up your development of new test without the need to simulate against a
real RISC-V processor::

    run --test=riscv_rand_instr_test --iss=spike,ovpsim
    run --test=riscv_rand_instr_test --iss=ovpsim,whisper
    run --test=riscv_rand_instr_test --iss=spike,sail

Run directed assembly/C tests
-----------------------------

Sometimes it might be useful to run some hand-coded assembly/C tests to hit some
corner cases::


    # Run a single/multiple assembly/C test
    run --asm_test asm_test_path1/asm_test1.S,asm_test_path2/asm_test2.S
    run --c_test c_test_path1/c_test1.c,c_test_path2/c_test2.c

    # Run regression with all assembly test(*.S)/ C test(*.c) under a given directory
    run --asm_test asm_test_path1,asm_test_path2
    run --c_test c_test_path1,c_test_path2

    # Run mix between the assembly/C test and assembly/C test under a directory
    run --asm_test asm_test_path1/asm_test1.S,asm_test_path2
    run --c_test c_test_path1/c_test1.c,c_test_path2

You could also use this approach to integrate the assembly/C tests
from other sources to riscv-dv flow.
