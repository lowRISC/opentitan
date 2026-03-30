# Life Cycle Controller Technical Specification
<!-- BEGIN CMDGEN util/mdbook_regression_links.py --hjson hw/ip/lc_ctrl/data/lc_ctrl.hjson --top earlgrey -->
| Regression | Version | [Stages](https://opentitan.org/book/doc/project_governance/development_stages.html) | Results |
|-|-|-|-|
 [`lc_ctrl_volatile_unlock_enabled`](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/dashboard.html) | 2.1.1 | D3, V1 | ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/lc_ctrl_volatile_unlock_enabled/test.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/lc_ctrl_volatile_unlock_enabled/passing.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/lc_ctrl_volatile_unlock_enabled/functional.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/lc_ctrl_volatile_unlock_enabled/code.svg) |
 [`lc_ctrl_volatile_unlock_disabled`](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/dashboard.html) | 2.1.1 | D3, V1 | ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/lc_ctrl_volatile_unlock_disabled/test.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/lc_ctrl_volatile_unlock_disabled/passing.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/lc_ctrl_volatile_unlock_disabled/functional.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/lc_ctrl_volatile_unlock_disabled/code.svg) |

This IP has been taped out in Earl Grey 1.0.0. The corresponding documentation and regression results can be found [here](https://opentitan.org/earlgrey_1.0.0/book/hw/ip/lc_ctrl/index.html).

<!-- END CMDGEN -->

# Overview

This document specifies the functionality of the life cycle controller.
The life cycle controller is a module that is a peripheral on the chip interconnect bus, and thus follows the [Comportability Specification](../../../doc/contributing/hw/comportability/README.md).
For the high-level description of the life cycle architecture of OpenTitan, please refer to the [Device Life Cycle Architecture](../../../doc/security/specs/device_life_cycle/README.md).
The life cycle implementation refers to the design that encompasses all life cycle functions.
This touches on the functionality of the following modules, listed in no particular order:
- The life cycle controller itself - A new peripheral
- The key manager
- The flash controller
- The OTP controller
- The reset / power controller
- The debug infrastructure, specifically TAP isolation
- Any other peripheral where life cycle information may alter its behavior

## Features

The life cycle controller provides the following features:
- Dedicated OTP interface to read and update the redundantly encoded device life cycle state.
- A CSR and a JTAG interface for initiating life cycle transitions.
- Dedicated concurrent decoding of the redundant life cycle state and broadcasting of redundantly encoded life cycle qualification signals (e.g., to enable DFT features or the main processor).
- A token hashing and matching mechanism to guard important life cycle transitions.
- An escalation receiver for the alert subsystem, which allows to invalidate the life cycle state as part of an escalation sequence (see also alert handler subsystem).

## Prelude - Why Not Software?

There are many ways to implement life cycle functions in a design.
This document opts for a more hardware driven approach, although there is still significant software hand holding required.

The question must be asked then, why not make it a completely software driven approach?
The life cycle states can be maintained simply as OTP variables, and ROM or a subsequent software stage can be responsible for choosing all subsequent behaviors.

There are a few reasons:
- This document strives to keep critical security functionality in hardware - either real gates or ROM.
- This document aims to keep the ROM as simple as required and not give it too much functionality.
Simple here refers to secure boot verification and jump.
- There is a life cycle escalation mechanism that temporarily alters the state when security vulnerabilities are detected.
It is difficult to manage this kind of fast escalation in software in our working model.
It is more suitable in hardware.
- Advancing life cycle state sometimes must be done in the absence of software for a variety of reasons; thus having a small piece of hardware that understands what to do is simpler than placing restrictions on the entire CPU / memory complex.
- As can be seen from this document, the hardware additions are small and non-complicated.
