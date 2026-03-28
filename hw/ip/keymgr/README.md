# Key Manager HWIP Technical Specification
<!-- BEGIN AUTOGEN from util/mdbook_regression_links.py -->
| Regression | Version | [Stages](https://opentitan.org/book/doc/project_governance/development_stages.html) | Results |
|-|-|-|-|
 [`keymgr`](https://nightly.reports.lowrisc.org/opentitan_weekly_earlgrey/2026_03_08/index.html) | 2.0.0 | D2S, V2S | <img src="https://img.shields.io/badge/Tests_Running-1110-blue"> <img src="https://img.shields.io/badge/Tests_Passing-96.85%25-brightgreen"> <img src="https://img.shields.io/badge/Functional_Coverage-91.16%25-brightgreen"> <img src="https://img.shields.io/badge/Code_Coverage-98.97%25-brightgreen"> |

This IP has been taped out in Earl Grey 1.0.0. The corresponding documentation and regression results can be found [here](https://opentitan.org/earlgrey_1.0.0/book/hw/ip/keymgr/index.html).
<!-- END AUTOGEN -->

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
