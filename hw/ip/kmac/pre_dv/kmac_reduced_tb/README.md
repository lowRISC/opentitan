KMAC Reduced Verilator Testbench
================================

This directory contains a very basic, scratch Verilator testbench of the SHA3 core and the PRNG instantiated inside KMAC.
The main use of this testbench is to help understanding how to operate and properly interface them, e.g., for evaluating security properties.

How to build and run the testbench
----------------------------------

From the OpenTitan top level execute

```sh
   fusesoc --verbose --cores-root=. run --setup --build lowrisc:dv_verilator:kmac_reduced_tb
```
to build the testbench and afterwards

```sh
   ./build/lowrisc_dv_verilator_kmac_reduced_tb_0/default-verilator/Vkmac_reduced_tb --trace
```
to run it.

Details of the testbench
------------------------

- `rtl/kmac_reduced_tb.sv`: SystemVerilog testbench, instantiates and drives the SHA3 core and the PRNG, checks whether the SHA3 core finishes without errors, signals test end and result
  (pass/fail) to C++ via output ports.
- `cpp/kmac_reduced_tb.cc`: Contains main function and instantiation of SimCtrl, reads output ports of DUT and signals simulation termination to Verilator.
