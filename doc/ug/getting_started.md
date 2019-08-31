# Getting started

Welcome!

This guide helps you to get started with the lowRISC Comportable chip designs.

## Conventions in this guide

This guide uses the environment variable `$REPO_TOP` to refer to the top-level of the git source tree.
The master tree is held on GitHub, this should be forked to user trees from which Pull Requests can be made.
There is a set of [Notes for using GitHub](github_notes.html).

## Setup

You can either follow the [install instructions](install_instructions.md) from start to end to install all software required to simulate the design with Verilator and build a bitstream for an FPGA with Xilinx Vivado or check the corresponding [design description](getting_started.md#choose-a-design-to-build) for install requirements.

## Choose a design to build

The code base contains multiple top-level designs, which can be synthesized or compiled for different targets.
A target can be a specific FPGA board, an ASIC technology, or a simulation tool.
The hardware you need to obtain and the tools you need to install depend on the chosen top-level design and the target.

In order to continue, choose a system from the [List of Systems](/doc/ug/system_list.html).
Read the design documentation for the requirements on the specific design/target combination, and then follow the appropriate steps below.

* [Build software](getting_started_sw.html)
* [Getting started with Verilator](getting_started_verilator.html)
* [Getting started on FPGAs](getting_started_fpga.html)
