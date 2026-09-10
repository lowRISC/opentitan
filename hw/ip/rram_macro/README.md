# RRAM macro HWIP Technical Specification

# Overview

This document specifies the RRAM macro hardware IP functionality.
The RRAM macro is a comportable IP that emulates a real RRAM macro.
This block is expected to be used in conjunction with the RRAM controller and cannot be used standalone.

## Features

The RRAM macro supports read and write commands to the RRAM.
In the open-source version, the RRAM is emulated with prim_ram_1p modules.
In the closed-source version, the real RRAM is instantiated and additional signals for production testing and scan isolation are connected.
The macro contains a CSR block for vendor specific operations which is not used in the open-source version.

## Replacing the macro

`rram_macro` is a FuseSoC virtual core (`lowrisc:virtual_ip:rram_macro`): this open-source implementation is the default, and a partner can map the virtual core to their own implementation instead, without changing anything outside `rram_macro` itself.
Since `earlgrey_pd_main.sv` instantiates `rram_macro` with a fixed parameter and port list, a replacement must match the open-source model exactly.


## Simulation

A pre-dv environment exists that allows to perform basic read and write transactions to the RRAM macro.
It can be started with dvsim:

`./util/dvsim/dvsim.py hw/ip/rram_macro/pre_dv/rram_macro_sim_cfg.hjson -i smoke`
