# Life Cycle Controller Technical Specification
<!-- BEGIN CMDGEN util/mdbook_regression_links.py --hjson hw/ip/lc_ctrl/data/lc_ctrl.hjson --top earlgrey -->
| Regression | Version | [Stages](https://opentitan.org/book/doc/project_governance/development_stages.html) | Results |
|-|-|-|-|
 [`lc_ctrl_volatile_unlock_enabled`](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/dashboard.html) | 2.2.0 | D2, V1 | ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/lc_ctrl_volatile_unlock_enabled/test.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/lc_ctrl_volatile_unlock_enabled/passing.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/lc_ctrl_volatile_unlock_enabled/functional.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/lc_ctrl_volatile_unlock_enabled/code.svg) |
 [`lc_ctrl_volatile_unlock_disabled`](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/dashboard.html) | 2.2.0 | D2, V1 | ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/lc_ctrl_volatile_unlock_disabled/test.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/lc_ctrl_volatile_unlock_disabled/passing.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/lc_ctrl_volatile_unlock_disabled/functional.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/lc_ctrl_volatile_unlock_disabled/code.svg) |

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
- The NVM controller, if present (the flash controller in Earl Grey 1.0, the RRAM controller in Earl Grey 2.0)
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

## Supported Parameter Sets

The following table lists the instantiation parameters of the life cycle controller.
Note that parameters prefixed with `RndCnst` are random netlist constants that need to be regenerated via topgen before the tapeout (typically by the silicon creator).

Parameter                        | Default             | Top Earlgrey                       | Description
---------------------------------|---------------------|------------------------------------|---------------
`AlertAsyncOn`                   | `{NumAlerts{1'b1}}` | Set by topgen                      | Adds synchronizers to the alert senders for an alert handler on another clock.
`AlertSkewCycles`                | `1`                 | `1`                                | Cycles of skew tolerated on the differential alert signals, set by topgen.
`SiliconCreatorId`               | `'0`                | `16'h4001`                         | Silicon creator ID exposed in the `HW_REVISION0` CSR.
`ProductId`                      | `'0`                | `16'h0010`                         | Product ID exposed in the `HW_REVISION0` CSR.
`RevisionId`                     | `'0`                | `8'h01`                            | Revision ID exposed in the `HW_REVISION1` CSR.
`IdcodeValue`                    | `32'h00000001`      | `jtag_id_pkg::LC_CTRL_JTAG_IDCODE` | Idcode for the LC JTAG TAP.
`UseDmiInterface`                | `1'b0`              | `1'b0`                             | Selects the TL-UL DMI port (`dmi_tl`) instead of the JTAG TAP to access the CSRs from the debug side.
`NumRmaAckSigs`                  | `2`                 | `2`                                | Number of RMA acknowledge inputs, set by topgen.
`SecVolatileRawUnlockEn`         | `0`                 | `0`                                | Enables the volatile RAW unlock feature. This is a feature for test chips only and must be disabled in production devices.
`EscNumSeverities`               | `4`                 | `4`                                | Number of escalation severities of the alert handler, set by topgen.
`EscPingCountWidth`              | `16`                | `16`                               | Width of the escalation ping counter of the alert handler, set by topgen.
`RndCnstLcKeymgrDivInvalid`      | (see RTL)           | (see RTL)                          | Diversification value used for all invalid life cycle states.
`RndCnstLcKeymgrDivTestUnlocked` | (see RTL)           | (see RTL)                          | Diversification value used for the TEST_UNLOCKED* life cycle states.
`RndCnstLcKeymgrDivDev`          | (see RTL)           | (see RTL)                          | Diversification value used for the DEV life cycle state.
`RndCnstLcKeymgrDivProduction`   | (see RTL)           | (see RTL)                          | Diversification value used for the PROD/PROD_END life cycle states.
`RndCnstLcKeymgrDivRma`          | (see RTL)           | (see RTL)                          | Diversification value used for the RMA life cycle state.
`RndCnstInvalidTokens`           | (see RTL)           | (see RTL)                          | Random values used for the invalid entries of the token mux.

The block-level testbench verifies the following parameter sets, which are signed off.

- `UseDmiInterface = 1'b0` and `NumRmaAckSigs = 2`, with `SecVolatileRawUnlockEn` set to `0` and to `1`.
  This is the configuration of Earl Grey, which uses `SecVolatileRawUnlockEn = 0`.
- `UseDmiInterface = 1'b1` and `NumRmaAckSigs = 1`, with `SecVolatileRawUnlockEn` set to `0` and to `1`.

The ID, IDCODE and random netlist constant parameters do not change the architecture, so any value of them is supported.

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
