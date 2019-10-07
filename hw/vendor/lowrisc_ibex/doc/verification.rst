Verification
============

Overview
--------

This is a SV/UVM testbench for the ibex core verification.
This testbench loads the instruction binary generated from open source random instruction generator `riscv-dv <https://github.com/google/riscv-dv>`_, runs the RTL simulation, and compares the instruction trace against ISS simulation.

Testbench component
~~~~~~~~~~~~~~~~~~~

-  Random instruction generator : `RISCV-DV <https://github.com/google/riscv-dv>`_
-  `Memory interface agent for instruction fetch and load/store
   operations <https://github.com/lowRISC/ibex/tree/master/dv/uvm/common/ibex_mem_intf_agent>`_
-  `Interrupt interface agent <https://github.com/lowRISC/ibex/tree/master/dv/uvm/common/irq_agent>`_
-  `Memory model <https://github.com/lowRISC/ibex/tree/master/dv/uvm/common/mem_model>`_
-  `Test and sequence library <https://github.com/lowRISC/ibex/tree/master/dv/uvm/tests>`_

Testplan
~~~~~~~~

The goal of this bench is to fully verify the ibex core with 100%
coverage. This includes all RV32IMC instructions testing, privileged
spec compliance, exception and interrupt testing, debug mode operations
etc. The complete test list can be found `here <https://github.com/lowRISC/ibex/blob/master/dv/uvm/riscv_dv_extension/testlist.yaml>`_.

Please note that this work is still working in progress.

Getting Started
---------------

Prerequisites
~~~~~~~~~~~~~

-  VCS RTL simulator (need to support UVM 1.2)
-  `Setup the RISC-V instruction generator and ISS sim environment <https://github.com/google/riscv-dv#getting-started>`_

End-to-end RTL/ISS co-simulation flow
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. figure:: images/dv-flow.png
   :alt: RTL/ISS co-simulation flow chart

   RTL/ISS co-simulation flow chart

The flow is controlled by a `Makefile <https://github.com/lowRISC/ibex/blob/master/dv/uvm/Makefile>`_, here’s the list of frequently
used commands:

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

You can add the compile/simulation options in `simulator.yaml <https://github.com/lowRISC/ibex/blob/master/dv/uvm/yaml/rtl_simulation.yaml>`_.

.. code-block:: bash

   # Use the new RTL simulator to run
   make ... SIMULATOR=xxx
