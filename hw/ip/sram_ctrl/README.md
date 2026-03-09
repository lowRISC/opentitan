# SRAM Controller Technical Specification
<!-- BEGIN AUTOGEN from util/mdbook_regression_links.py -->
| Regression | Version | [Stages](https://opentitan.org/book/doc/project_governance/development_stages.html) | Results |
|-|-|-|-|
 [`sram_ctrl_main`](https://nightly.reports.lowrisc.org/opentitan_weekly_earlgrey/2026_03_08/index.html) | 1.1.0 | D3, V2S | <img src="https://img.shields.io/badge/Tests_Running-1190-blue"> <img src="https://img.shields.io/badge/Tests_Passing-97.98%25-brightgreen"> <img src="https://img.shields.io/badge/Functional_Coverage-98.33%25-brightgreen"> <img src="https://img.shields.io/badge/Code_Coverage-96.15%25-brightgreen"> |
 [`sram_ctrl_ret`](https://nightly.reports.lowrisc.org/opentitan_weekly_earlgrey/2026_03_08/index.html) | 1.1.0 | D3, V2S | <img src="https://img.shields.io/badge/Tests_Running-1190-blue"> <img src="https://img.shields.io/badge/Tests_Passing-98.32%25-brightgreen"> <img src="https://img.shields.io/badge/Functional_Coverage-98.33%25-brightgreen"> <img src="https://img.shields.io/badge/Code_Coverage-96.12%25-brightgreen"> |

This IP has been taped out in Earl Grey 1.0.0. The corresponding documentation and regression results can be found [here](https://opentitan.org/earlgrey_1.0.0/book/hw/ip/sram_ctrl/index.html).
<!-- END AUTOGEN -->

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
