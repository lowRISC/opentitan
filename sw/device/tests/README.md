---
title: "Software Tests Readme"
---

# Overview

This directory contains a suite of self-contained tests that are capable of running across all of OpenTitan's verification platforms.
These platforms include - UVM DV, Verilator DV, FPGA, and eventually silicon.

To enable this cross-platform testing, each test is self-contained and do not require additional host or backend resources to verify correct behavior.
This suggests that any testing that would involve emulation of host capability, such as an external SPI host or an external host to encrypt/decrypt data, is not appropriate for these types of self-contained tests.
It is assumed those tests will live in a different directory as the host emulation will be different for each verification target.
For FPGA / silicon this may be a host machine, while for UVM / Verilator this may be some kind of SystemVerilog back-end.

## Self Checking Mechanism

The self-checking mechanism is accomplished by invoking one of the test status indication APIs defined in `sw/device/lib/testing/test_status.h`.
It is mandatory to invoke either `test_failed()` or `test_passed()` based on the checks performed in the test.
These methods provide a platform-agnostic way to indicate the test status.
Invoking these methods also causes the core to abort the execution and never return after reaching one of these terminal states.

For non-UVM DV platforms (Verilator DV, FPGA or silicon), these methods write a message to the console.
When the tests pass, it will output `PASS!\r\n`.
The capturing and generation of this message will differ per testing target.
On FPGA / silicon, they will feed directly to a host machine through a physical UART connection, where the host can decipher the message correctness.
On Verilator, they will feed to a virtual UART terminal where the host can do the same.

For UVM DV, these methods write the test status signature to a known location in the memory, which is monitored by the testbench.

# List of Tests

{{< testplan "hw/top_earlgrey/data/standalone_sw_testplan.hjson" >}}
