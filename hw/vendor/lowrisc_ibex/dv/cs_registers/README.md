Ibex simulation Control/Status Registers Testbench
==================================================

This directory contains a basic sample testbench in C++ for testing correctness of some CS registers implemented in Ibex.

It is a work in progress and only tests a handful of registers, and is missing many features.

How to build and run the testbench
----------------------------------

Verilator version:

   ```sh
   fusesoc --cores-root=. run --target=sim --tool=verilator lowrisc:ibex:tb_cs_registers
   ```
VCS version:

   ```sh
   fusesoc --cores-root=. run --target=sim --tool=vcs lowrisc:ibex:tb_cs_registers
   ```

Testbench file structure
------------------------

`tb/tb_cs_registers.sv` - Is the verilog top level, it instantiates the DUT and DPI calls

`tb/tb_cs_registers.cc` - Is the C++ top level, it sets up the testbench components

`driver/` - Contains components to generate and drive random register transactions

`env/` - Contains components to generate and drive other signals

`model/` - Contains a model of the register state and checking functions

DPI methodology
---------------

The testbench relies on DPI calls to interface between the RTL and the C++ driver/checker components.
This methodology allows the testbench to support both Verilator and commercial simulators.

Each DPI call has a function in SV (which is called in the SV top-level), and a corresponding C function.
To support the instantiation of multiple instances of TB components, some DPI modules can register their objects referenced by name.
Each DPI call from the RTL then calls into the correct instance by matching the name.

Testbench structure
-------------------

The driver component contains one DPI "interface" to drive new random transactions into the DUT, and another to monitor issued transactions including the DUT's responses.
Each time a new transaction is detected by the monitor component, it is captured and sent to the model.
The model reads incoming transactions, updates its internal state and checks that the DUT outputs matches its own predictions.

