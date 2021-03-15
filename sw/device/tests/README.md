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

## Signaling the end of test and self-checking mechanism

It is mandatory to invoke the platform-agnostic API `test_status_set()` to explicitly signal the end of the test based on whether it passed or failed.
When invoked, the API calls `abort()` at the end to stop the core from executing any further.
Please see `sw/device/lib/testing/test_status.h` for documentation and usage.

In non-DV platforms (Verilator DV, FPGA or silicon), the signal is a message written to the console.
It will output `PASS!\r\n` when the tests pass and `FAIL!\r\n` when they fail.
How these console messages are captured differs based on the testing target.
On FPGA / silicon, they will feed directly to a host machine through a physical UART connection, where the host can decipher the message correctness.
On Verilator, they will feed to a virtual UART terminal where the host can do the same.

In UVM DV, the test status is written to a known location in the memory, which is monitored by the testbench.
Based on the captured value, the testbench monitor invokes UVM methods to pass or fail the test.

# List of Tests

{{< incGenFromIpDesc "/hw/top_earlgrey/data/standalone_sw_testplan.hjson" "testplan" >}}
