Trivium/Bivium Stream Cipher Verilator Testbench
================================================

This directory contains a basic, scratch Verilator testbench targeting
functional verification of the Trivium/Bivium stream cipher primitives
during development.

How to build and run the testbench
----------------------------------

From the OpenTitan top level execute

   ```sh
   fusesoc --cores-root=. run --setup --build \
     lowrisc:dv_verilator:prim_trivium_tb
   ```
to build the testbench and afterwards

   ```sh
   ./build/lowrisc_dv_verilator_prim_trivium_tb_0/default-verilator/Vprim_trivium_tb \
     --trace
   ```
to run it.

Details of the testbench
------------------------

- `rtl/prim_trivium_tb.sv`: SystemVerilog testbench, instantiates and
  drives multiple, differently parameterized instances of the primitives,
  checks key streams of the Trivium instances against a known good key
  stream, signals test end and result (pass/fail) to C++ via output ports.
  Change this file to e.g. configure different output widths.
- `cpp/prim_trivium_tb.cc`: Contains main function and instantiation of
  SimCtrl, reads output ports of the testbench and signals simulation
  termination to Verilator.
