Verification
============

Overview
--------

This is a SV/UVM testbench for verification of the Ibex core.
At a high level, this testbench uses the open source `RISCV-DV random instruction generator
<https://github.com/google/riscv-dv>`_ to generate compiled instruction binaries, loads them into a
simple memory model, stimulates the Ibex core to run this program in memory, and then compares the
core trace log against a golden model ISS trace log to check for correctness of execution.

Testbench Architecture
----------------------

As previously mentioned, this testbench has been constructed based on its usage of the RISCV-DV
random instruction generator developed by Google.
A block diagram of the testbench is below.

.. figure:: images/tb.svg
    :alt: Testbench Architecture

    Architecture of the UVM testbench for Ibex core

Memory Interface Agents
~~~~~~~~~~~~~~~~~~~~~~~

The code can be found in the `dv/uvm/common/ibex_mem_intf_agent
<https://github.com/lowRISC/ibex/tree/master/dv/uvm/common/ibex_mem_intf_agent>`_ directory.
Two of these agents are instantiated within the testbench, one for the instruction fetch interface,
and the second for the LSU interface.
These agents run slave sequences that wait for memory requests from the core, and then grant the
requests for instructions or for data.

Interrupt Interface Agent
~~~~~~~~~~~~~~~~~~~~~~~~~

The code can be found in the
`dv/uvm/common/irq_agent <https://github.com/lowRISC/ibex/tree/master/dv/uvm/common/irq_agent>`_ directory.
This agent is used to drive stimulus onto the Ibex core's interrupt pins randomly during test
execution.

Memory Model
~~~~~~~~~~~~

The code can be found in the
`dv/uvm/common/mem_model <https://github.com/lowRISC/ibex/tree/master/dv/uvm/common/mem_model>`_
directory.
The testbench instantiates a single instance of this memory model that it loads the compiled
assembly test program into at the beginning of each test.
This acts as a unified instruction/data memory that serves all requests from both of the
memory interface agents.

Test and Sequence Library
~~~~~~~~~~~~~~~~~~~~~~~~~

The code can be found in the
`dv/uvm/tests <https://github.com/lowRISC/ibex/tree/master/dv/uvm/tests>`_ directory.
The tests here are the main sources of external stimulus generation and checking for this testbench,
as the memory interface slave sequences simply serve the core's memory requests.
The tests here are all extended from ``core_ibex_base_test``, and coordinate the entire flow for a
single test, from loading the compiled assembly binary program into the testbench memory model, to
checking the Ibex core status during the test and dealing with test timeouts.
The sequences here are used to drive interrupt and debug stimulus into the core.

Testplan
~~~~~~~~

The goal of this bench is to fully verify the Ibex core with 100%
coverage. This includes testing all RV32IMC instructions, privileged
spec compliance, exception and interrupt testing, Debug Mode operation etc.
The complete test list can be found in the file `dv/uvm/riscv_dv_extension/testlist.yaml
<https://github.com/lowRISC/ibex/blob/master/dv/uvm/riscv_dv_extension/testlist.yaml>`_.

Please note that verification is still a work in progress.

Getting Started
---------------

Prerequisites & Environment Setup
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- VCS RTL simulator (needed to support UVM 1.2)
- RISCV-DV Prerequisites - https://github.com/google/riscv-dv#prerequisites
- GCC setup - https://github.com/google/riscv-dv#compile-generated-programs-with-gcc
- ISS setup - https://github.com/google/riscv-dv#run-iss-instruction-set-simulator-simulation - note that commit log must be enabled in spike by passing ``--enable-commitlog`` to the configure script.

End-to-end RTL/ISS co-simulation flow
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. figure:: images/dv-flow.png
   :alt: RTL/ISS co-simulation flow chart

   RTL/ISS co-simulation flow chart

The last stage in this flow handles log comparisons to determine correctness of a given simulation.
To do this, both the trace log produced by the core and the trace log produced by the chosen golden
model ISS are parsed to collect information about all register writebacks that occur.
These two sets of register writeback data are then compared to verify that the core is writing the
correct data to the correct registers in the correct order.

However, this checking model quickly falls apart once situations involving external stimulus (such
as interrupts and debug requests) start being tested, as while ISS models can simulate traps due to
exceptions, they cannot model traps due to external stimulus.
In order to provide support for these sorts of scenarios to verify if the core has entered the
proper interrupt handler, entered Debug Mode properly, updated any CSRs correctly, and so on, the
handshaking mechanism provided by the RISCV-DV instruction generator is heavily used, which
effectively allows the core to send status information to the testbench during program execution for
any analysis that is required to increase verification effectiveness.
This mechanism is explained in detail at https://github.com/google/riscv-dv/blob/master/HANDSHAKE.md.
As a sidenote, the signature address that this testbench uses for the handshaking is ``0x8ffffffc``.
Additionally, as is mentioned in the RISCV-DV documentation of this handshake, a small set of API
tasks are provided in `dv/uvm/tests/core_ibex_base_test.sv
<https://github.com/lowRISC/ibex/blob/master/dv/uvm/tests/core_ibex_base_tests.sv>`_ to enable easy
and efficient integration and usage of this mechanism in this test environment.
To see how this handshake is used during real simulations, look in
`dv/uvm/tests/core_ibex_test_lib.sv
<https://github.com/lowRISC/ibex/blob/master/dv/uvm/tests/core_ibex_test_lib.sv>`_.
As can be seen, this mechanism is extensively used to provide runtime verification for situations involving external debug
requests, interrupt assertions, and memory faults.
To add another layer of correctness checking to the checking already provided by the handshake
mechanism, a modified version of the trace log comparison is used, as comparing every register write
performed during the entire simulation will lead to an incorrect result since the ISS trace log will
not contain any execution information in the debug ROM or in any interrupt handler code.
As a result, only the final values contained in every register at the end of the test are compared
against each other, since any code executed in the debug ROM and trap handlers should not corrupt
register state in the rest of the program.

The entirety of this flow is controlled by the Makefile found at
`dv/uvm/Makefile <https://github.com/lowRISC/ibex/blob/master/dv/uvm/Makefile>`_; here is a list of frequently used commands:

.. code-block:: bash

   # Run a full regression
   make

   # Run a full regression, redirect the output directory
   make OUT=xxx

   # Run a single test
   make TEST=riscv_machine_mode_rand_test ITERATIONS=1

   # Run a test with a specific seed, dump waveform
   make TEST=riscv_machine_mode_rand_test ITERATIONS=1 SEED=123 WAVES=1

   # Verbose logging
   make ... VERBOSE=1

   # Run multiple tests in parallel through LSF
   make ... LSF_CMD="bsub -Is"

   # Get command reference of the simulation script
   python3 sim.py --help

   # Generate the assembly tests only
   make gen

   # Pass addtional options to the generator
   make GEN_OPTS="xxxx"  ...

   # Compile and run RTL simulation
   make TEST=xxx compile,rtl_sim

   # Use a different ISS (default is spike)
   make ... ISS=ovpsim

   # Run a full regression with coverage
   make COV=1

Run with a different RTL simulator
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

You can add any compile/runtime options in `dv/uvm/yaml/simulator.yaml
<https://github.com/lowRISC/ibex/blob/master/dv/uvm/yaml/rtl_simulation.yaml>`_.

.. code-block:: bash

   # Use the new RTL simulator to run
   make ... SIMULATOR=xxx
