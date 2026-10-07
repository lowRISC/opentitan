# Interrupt Controller Technical Specification
% if topname == "earlgrey":

This IP has been taped out in Earl Grey 1.0.0. The corresponding documentation can be found [here](https://opentitan.org/earlgrey_1.0.0/book/hw/top_earlgrey/ip_autogen/rv_plic/index.html).
% endif

# Overview

This document specifies the Interrupt Controller (RV_PLIC) functionality. This
module conforms to the
[Comportable guideline for peripheral functionality](../../../../doc/contributing/hw/comportability/README.md).
See that document for integration overview within the broader top level system.


${"##"} Features

- RISC-V Platform-Level Interrupt Controller (PLIC) compliant interrupt controller
- Support arbitrary number of interrupt vectors (up to 1023) and targets
- Support interrupt enable, interrupt status registers
- Memory-mapped MSIP register per HART for software interrupt control.

${"##"} Description

The RV_PLIC module is designed to manage various interrupt sources from the
peripherals. It receives interrupt events as either edge or level of the
incoming interrupt signals (``intr_src_i``) and can notify multiple targets.

${"##"} Compatibility

The RV_PLIC is compatible with any RISC-V core implementing the RISC-V privilege specification.
