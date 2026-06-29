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

## Simulation

A pre-dv environment exists that allows to perform basic read and write transactions to the RRAM macro.
It can be started with dvsim:

`./util/dvsim/dvsim.py hw/ip/rram_macro/pre_dv/rram_macro_sim_cfg.hjson -i smoke`
