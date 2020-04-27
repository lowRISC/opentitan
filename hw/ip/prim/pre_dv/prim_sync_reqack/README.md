REQ/ACK Syncronizer Verilator Testbench
=======================================

This directory contains a basic, scratch Verilator testbench targeting
functional verification of the REQ/ACK synchronizer primitive during
development.

How to build and run the testbench
----------------------------------

From the OpenTitan top level execute

   ```sh
   fusesoc --cores-root=. run --setup --build \
     lowrisc:dv_verilator:prim_sync_reqack_tb
   ```
to build the testbench and afterwards

   ```sh
   ./build/lowrisc_dv_verilator_prim_sync_reqack_tb_0/default-verilator/Vprim_sync_reqack_tb \
     --trace
   ```
to run it.

Details of the testbench
------------------------

- `rtl/prim_sync_reqack_tb.sv`: SystemVerilog testbench, instantiates and
  drives the DUT, counts handshakes in both domains, signals test end and
  result (pass/fail) to C++ via output ports. Change this file to e.g.
  for a different clock ratio or more transactions.
- `cpp/prim_sync_reqack_tb.cc`: Contains main function and instantiation of
  SimCtrl, reads output ports of DUT and signals simulation termination to
  Verilator.
