# Key Manager HWIP Technical Specification
<!-- BEGIN CMDGEN util/mdbook_regression_links.py --hjson hw/ip/keymgr/data/keymgr.hjson --top earlgrey -->
| Regression | Version | [Stages](https://opentitan.org/book/doc/project_governance/development_stages.html) | Results |
|-|-|-|-|
 [`keymgr`](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/dashboard.html) | 2.0.0 | D2S, V2S | ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/keymgr/test.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/keymgr/passing.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/keymgr/functional.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/keymgr/code.svg) |

This IP has been taped out in Earl Grey 1.0.0. The corresponding documentation and regression results can be found [here](https://opentitan.org/earlgrey_1.0.0/book/hw/ip/keymgr/index.html).

<!-- END CMDGEN -->

# Overview

This document specifies the functionality of the OpenTitan key manager.

## Features

- One-way key and identity (working) state hidden from software.
- Version controlled identity and key generation.
- Key generation for both software consumption and hardware sideload.
- Support for DICE open profile.


## Description

The key manager implements the hardware component of the [identities and root keys](../../../doc/security/specs/identities_and_root_keys/) strategy of OpenTitan.

It enables the system to shield critical assets from software directly and provides a simple model for software to use derived key and identity outputs.
