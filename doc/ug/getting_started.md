---
title: "Getting Started"
---

Welcome!

This guide helps you to get started with OpenTitan.

## OpenTitan Repository

The [OpenTitan Repository](https://github.com/lowRISC/opentitan) must be checked out locally.
If you wish to contribute to OpenTitan you will need to make a fork on GitHub, otherwise you can just locally clone the main repository.
There is a set of [notes for using GitHub]({{< relref "github_notes.md" >}}) which explains how to work with your own fork.

**Throughout the documentation `$REPO_TOP` refers to the path where the OpenTitan repository is checked out**

## Setup

You can either follow the [install instructions]({{< relref "install_instructions" >}}) from start to end to install all software required to simulate the design with Verilator and build a bitstream for an FPGA with Xilinx Vivado or check the corresponding [design description]({{< relref "getting_started.md#choose-a-design-to-build" >}}) for install requirements.

## Choose a design to build

The code base contains multiple top-level designs, which can be synthesized or compiled for different targets.
A target can be a specific FPGA board, an ASIC technology, or a simulation tool.
The hardware you need to obtain and the tools you need to install depend on the chosen top-level design and the target.

In order to continue, choose a system from the [List of Systems]({{< relref "/doc/ug/system_list.md" >}}).
Read the design documentation for the requirements on the specific design/target combination, and then follow the appropriate steps below.

* [Build software]({{< relref "getting_started_sw.md" >}})
* [Getting started with Verilator]({{< relref "getting_started_verilator.md" >}})
* [Getting started on FPGAs]({{< relref "getting_started_fpga.md" >}})

## Understanding device software flow
This section discusses the general software operating flow.

Under the sw directory, there are numerous sub-directories each containing code for different purposes.
In general however, software execution can be divided into two execution stages - ROM and embedded memory (currently emulated embedded flash).

The ROM stage software, built from `sw/device/boot_rom` is always run first on all platforms (DV / Verilator / FPGA).
In DV / Verilator, both the ROM and embedded memory contents are backdoor loaded into their respective storage, thus the ROM code simply checks for the presence of code and jumps to it.
ROM at the moment does not perform validation of the backdoor loaded code.

On FPGA, we do not backdoor load the embedded memory.
Instead, the ROM code proceeds through a code download process where a [host]({{< relref "/sw/host/spiflash/README.md" >}}) feeds an image frame by frame.
The ROM code then integrity checks each received image and programs it into the embedded memory.
At the conclusion of this process, the ROM then jumps to the newly downloaded executable code.
Again, just like the DV / Verilator case, there is currently no additional validation of the downloaded code.
That feature is expected to be added later.
