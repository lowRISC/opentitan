TLUL/Shim Verilator Testbench
=======================

This directory contains the Verilator testbench for the TLUL shim adapter that is attached
to the AES IP block, run in the GCM mode.


How to build and run the example
--------------------------------

To build the testbench, execute from the OpenTitan top level:

```sh
fusesoc --cores-root=. --verbose run --setup --build lowrisc:dv_verilator:aes_tlul_shim_tb
```
To execute the obtained Verilator binary and with trace generation, run:

```sh
./build/lowrisc_dv_verilator_aes_tlul_shim_tb_0/default-verilator/Vaes_tlul_shim_tb --trace
```

Details of the testbench
------------------------

- cpp/aes\_tlul\_shim\_tb.cc: contains main function and instantiation of SimCtrl
- rtl/aes\_tlul\_shim\_tb.sv: contains the testbench logic
- rtl/aes\_tlul\_delayer\_tb.sv: contains an optional delayer module to artificially induce random delays between the Shim and the TLUL bus.
- rtl/aes\_tlul\_shim\_tb_reqs.sv: contains requests (stimuli) that are fed to the testbench.
- rtl/aes\_tlul\_shim\_tb_pkg.sv: contains common parameters and functions.
