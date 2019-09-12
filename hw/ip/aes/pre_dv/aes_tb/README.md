AES Verilator Testbench
=======================

This directory contains a basic Verilator testbench in C++ targeting functional
verficiation of the AES unit during the design phase.

It comes with an TLUL interface class to control the AES module through the
register interface.

How to build and run the example
--------------------------------

From the OpenTitan top level:

   ```sh
   fusesoc --cores-root=. run --setup --build lowrisc:dv_verilator:aes_sim
   ./build/lowrisc_dv_verilator_aes_sim_0.6/default-verilator/Vaes_sim --trace
   ```

Details of the testbench
------------------------

- cpp/aes\_tb.cc: contains main function and instantiation of SimCtrl
- cpp/aes\_tlul_interface.cc: contains functions to control the TLUL
  interface of the testbench as well as the sequence of transcations
