Ascon Duplex Verilator Testbench
================================

This directory contains a basic, scratch Verilator testbench targeting
functional verification of the Ascon duplex implementations during
development.

How to build and run the testbench
----------------------------------

From the OpenTitan top level execute

   ```sh
   fusesoc --cores-root=. run --setup --build lowrisc:dv_verilator:prim_ascon_duplex_tb
   ```
to build the testbench and afterwards

   ```sh
   ./build/lowrisc_dv_verilator_prim_ascon_duplex_tb_0/default-verilator/Vprim_ascon_duplex_tb \
     --trace
   ```
to run it.

Details of the testbench
------------------------

- `rtl/prim_ascon_duplex_tb.sv`: SystemVerilog testbench, signals test end and
  result (pass/fail) to C++ via output ports.
- `cpp/prim_ascon_duplex_tb.cc`: Contains main function and instantiation of SimCtrl,
  reads output ports of DUT and signals simulation termination to Verilator.
