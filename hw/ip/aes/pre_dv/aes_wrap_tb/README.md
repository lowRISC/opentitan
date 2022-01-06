AES Wrap Verilator Testbench
============================

This directory contains a basic, scratch Verilator testbench targeting
functional verification of the AES wrapper.

How to build and run the testbench
----------------------------------

From the OpenTitan top level execute

   ```sh
   fusesoc --cores-root=. run --setup --build lowrisc:dv_verilator:aes_wrap_tb
   ```
to build the testbench and afterwards

   ```sh
   ./build/lowrisc_dv_verilator_aes_wrap_tb_0/default-verilator/Vaes_wrap_tb \
     --trace
   ```
to run it.

Details of the testbench
------------------------

- `rtl/aes_wrap_tb.sv`: SystemVerilog testbench, instantiates and drives the
  different AES wrapper, compares outputs, signals test end and result
  (pass/fail) to C++ via output ports.
- `cpp/aes_wrap_tb.cc`: Contains main function and instantiation of SimCtrl,
  reads output ports of DUT and signals simulation termination to Verilator.
