Ascon Verilator Testbench
=======================

This directory contains a basic Verilator testbench in C++ targeting functional
verification of the Ascon unit during the design phase.


How to build and run the example
--------------------------------

From the OpenTitan top level:

   ```sh
   fusesoc --cores-root=. run --setup --build lowrisc:dv_verilator:ascon_sim
   ```
to build the testbench and afterwards

   ```sh
   ./build/lowrisc_dv_verilator_ascon_sim_0.1/default-verilator/Vascon_sim --trace
   ```

Details of the testbench
------------------------

- cpp/ascon\_tb.cc: contains main function and instantiation of SimCtrl
