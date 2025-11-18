# Interrupt Controller Technical Specification

# Overview

This document specifies the Interrupt Controller (RV_PLIC) functionality. This
module conforms to the
[Comportable guideline for peripheral functionality](../../../../doc/contributing/hw/comportability/README.md).
See that document for integration overview within the broader top level system.


## Features

- RISC-V Platform-Level Interrupt Controller (PLIC) compliant interrupt controller
- Support arbitrary number of interrupt vectors (up to 1023) and targets
- Support interrupt enable, interrupt status registers
- Memory-mapped MSIP register per HART for software interrupt control.

## Description

The RV_PLIC module is designed to manage various interrupt sources from the
peripherals. It receives interrupt events as either edge or level of the
incoming interrupt signals (``intr_src_i``) and can notify multiple targets.

Note that the lowest bit of ``intr_src_i`` is ignored because it corresponds
interrupt ID 0 which is reserved to mean "no interrupt".

## Compatibility

The RV_PLIC is compatible with any RISC-V core implementing the RISC-V privilege specification.
