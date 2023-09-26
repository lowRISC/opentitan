# SRAM Controller Technical Specification

[`sram_ctrl/main`](https://reports.opentitan.org/hw/ip/sram_ctrl_main/dv/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/sram_ctrl/main/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/sram_ctrl/main/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/sram_ctrl/main/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/sram_ctrl/main/code.svg)

[`sram_ctrl/ret`](https://reports.opentitan.org/hw/ip/sram_ctrl_ret/dv/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/sram_ctrl/ret/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/sram_ctrl/ret/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/sram_ctrl/ret/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/sram_ctrl/ret/code.svg)

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
