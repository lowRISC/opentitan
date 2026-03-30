# SRAM Controller Technical Specification
<!-- BEGIN CMDGEN util/mdbook_regression_links.py --hjson hw/ip/sram_ctrl/data/sram_ctrl.hjson --top earlgrey -->
| Regression | Version | [Stages](https://opentitan.org/book/doc/project_governance/development_stages.html) | Results |
|-|-|-|-|
 [`sram_ctrl_main`](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/dashboard.html) | 1.1.0 | D3, V2S | ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/sram_ctrl_main/test.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/sram_ctrl_main/passing.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/sram_ctrl_main/functional.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/sram_ctrl_main/code.svg) |
 [`sram_ctrl_ret`](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/dashboard.html) | 1.1.0 | D3, V2S | ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/sram_ctrl_ret/test.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/sram_ctrl_ret/passing.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/sram_ctrl_ret/functional.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/sram_ctrl_ret/code.svg) |

This IP has been taped out in Earl Grey 1.0.0. The corresponding documentation and regression results can be found [here](https://opentitan.org/earlgrey_1.0.0/book/hw/ip/sram_ctrl/index.html).

<!-- END CMDGEN -->

# Overview

This document specifies the functionality of the SRAM memory controller.
The SRAM controller is a module that is a peripheral on the chip interconnect bus, and thus follows the [Comportability Specification](../../../doc/contributing/hw/comportability/README.md).


The SRAM controller contains the SRAM data and address scrambling device and provides CSRs for requesting the scrambling keys and triggering the hardware initialization feature.

## Features

- [Lightweight scrambling mechanism](../prim/doc/prim_ram_1p_scr.md#custom-substitution-permutation-network) based on the PRINCE cipher.
- Key request logic for the lightweight memory and address scrambling device.
- Alert sender and checking logic for detecting bus integrity failures.
- LFSR-based memory initialization feature.
- Access controls to allow / disallow code execution from SRAM.
- Security hardening when integrity error has been detected.
- Optional memory readback mode for detecting memory integrity errors.
