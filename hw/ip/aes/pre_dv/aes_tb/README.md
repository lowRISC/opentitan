# TLUL/Shim Verilator Testbench

This directory contains the Verilator testbench for the AES IP block.
Out of the box, the testbench contains test vectors for most of the salient use cases, nonetheless extending the testbench with further tests is straightforward as detailed below.
By default, communication with the IP happens over the TLUL bus.
If a TLUL/shim adapter is available, messages can optionally be relayed by the shim.

## Current Test Vectors

The `./data` directory contains an array of `.svh` files each of them containing a single set of input stimuli that constitute a test:

```
data
├── gcm_k128_a0_d0.svh    # AES-GCM-128 Encryption; 0 AD Bytes; 0 Msg Bytes
├── gcm_k128_a0_d16.svh   # AES-GCM-128 Encryption; 0 AD Bytes; 16 Msg Bytes
├── gcm_k128_a20_d60.svh  # AES-GCM-128 Encryption/Decryption/Save/Restore; 20 AD Bytes; 60 Msg Bytes
├── gcm_k128_a20_d64.svh  # AES-GCM-128 Encryption; 20 AD Bytes; 64 Msg Bytes
└── modes_d64.svh         # AES-{128,192,256}-{ECB,CBC,OFB,CFB,CTR} Encryption/Decryption
```

### Adding/Modifying Tests

Each test vector file `./data/*.svh` starts with a preamble that instruments both the testbench RTL as well as the `c_dpi` model:

```systemverilog
`define AD_LENGTH    // Number of AD bytes
`define MSG_LENGTH   // Number of Msg bytes
`define NUM_REQUESTS // Total number of requests
```

Here, `NUM_REQUESTS` denotes the number of `read_request`, `write_request` and `c_dpi_load` invocations within the file.
Having written a new test vector file, the `fusesoc` configuration needs to be made aware of it.

1. Add the `.svh` filename to the list of RTL files under `files_rtl/files`.
2. Add the `.svh` filename to the `DREQUESTS_FILE` Verilator variable under `verilator/verilator_options`.

## Building and Running the Verilator Testbench

To build the testbench, execute from the OpenTitan top level:

```sh
fusesoc --cores-root=. --verbose run --setup --build lowrisc:dv_verilator:aes_tb
```
To execute the obtained Verilator binary and with trace generation, run:

```sh
./build/lowrisc_dv_verilator_aes_tb_0/default-verilator/Vaes_tb --trace
```

## Details of the testbench

- cpp/aes\_tb.cc: contains main function and instantiation of SimCtrl
- rtl/aes\_tb.sv: contains the testbench logic
- rtl/tlul\_delayer.sv: contains an optional delayer module to artificially induce random delays in the TLUL bus.
- rtl/tlul\_adapter_tb_reqs.sv: is an adapter than converts generic read/write requests into TLUL requests.
- rtl/aes\_tb_reqs.sv: contains requests (stimuli) that are fed to the testbench.
- rtl/aes\_tb_pkg.sv: contains common parameters and functions.
- data/*: contains test vector files.
