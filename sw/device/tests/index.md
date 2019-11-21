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

Currently, the self-checking mechanism is accomplished through a console message.
When the tests pass, it will output `PASS!\r\n`.

The capturing and generation of this message will differ per testing target.
On FPGA / silicon, they will feed directly to a host machine through a physical UART conection, where the host can decipher the message correctness.
On Verilator, they will feed to a virtual UART terminal where the host can do the same.
On DV, they will feed to a fixed memory location where the DV backend can efficiently pick up the message without significant parsing overhead.

# List of Tests

{{< testplan "hw/top_earlgrey/data/standalone_sw_testplan.hjson" >}}
