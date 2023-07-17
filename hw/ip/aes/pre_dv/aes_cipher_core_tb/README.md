AES Cipher Core Verilator Testbench
===================================

This directory contains a very basic, scratch Verilator testbench of the AES
cipher core. The main use of this testbench is to help understanding how
to operate and properly interface the AES cipher core, e.g., for evaluating
security properties.

How to build and run the testbench
----------------------------------

From the OpenTitan top level execute

   ```sh
   fusesoc --cores-root=. run --setup \
     --build lowrisc:dv_verilator:aes_cipher_core_tb
   ```
to build the testbench and afterwards

   ```sh
   ./build/lowrisc_dv_verilator_aes_cipher_core_tb_0/default-verilator/Vaes_cipher_core_tb \
     --trace
   ```
to run it.

Details of the testbench
------------------------

- `rtl/aes_cipher_core_tb.sv`: SystemVerilog testbench, instantiates and drives
  the AES cipher core, compares outputs, signals test end and result
  (pass/fail) to C++ via output ports.
- `cpp/aes_cipher_core_tb.cc`: Contains main function and instantiation of
  SimCtrl, reads output ports of DUT and signals simulation termination to
  Verilator.
