SHA-2 Verilator Testbenches
===================================

This directory contains Verilator testbenches of the 2 variants of the SHA-2 engine prim: 256-only (MultimodeEn = 0) and the multi-mode engine (MultimodeEn = 1).
The main purpose of these testbenches is to instantiate the SHA-2 engine and test it with preset test vectors and compare the computed digest with the expected hash, and to scope how an integrating IP would need to interface with the SHA-2 engine.

How to build and run the testbenches
-----------------------------------

From the OpenTitan top level execute

   ```sh
   fusesoc --verbose --cores-root=. run --setup
       --build lowrisc:dv_verilator:prim_sha_tb
   ```
to build the testbench with output for linting warnings and afterwards

   ```sh
   ../build/lowrisc_dv_verilator_prim_sha_tb_0/default-verilator/Vprim_sha_tb
     --trace
   ```
to run the 256-only SHA-2 testbench.

-----------------------------------

```sh
   fusesoc --verbose --cores-root=. run --setup
       --build lowrisc:dv_verilator:prim_sha_multimode32_tb
   ```
to build the testbench with output for linting warnings and afterwards

   ```sh
   ../build/lowrisc_dv_verilator_prim_sha_multimode32_tb_0/default-verilator/Vprim_sha_multimode32_tb
     --trace
   ```
to run the multi-mode SHA-2 testbench.


Details of the testbenches
-----------------------------------

- `rtl/prim_sha_tb.sv`: SystemVerilog testbench, instantiates and drives the SHA-2 256 engine, compares outputs, signals test end and result (pass/fail) to C++ via output ports.
- `cpp/prim_sha_tb.cc`: Contains main function and instantiation of SimCtrl, reads output ports of DUT and signals simulation termination to Verilator.

- `rtl/prim_sha_multimode32_tb.sv`: SystemVerilog testbench, instantiates and drives the multi-mode SHA-2 engine, compares outputs, signals test end and result (pass/fail) to C++ via output ports.
- `cpp/prim_sha_multimode32_tb.cc`: Contains main function and instantiation of SimCtrl, reads output ports of DUT and signals simulation termination to Verilator.
