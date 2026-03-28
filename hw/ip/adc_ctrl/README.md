# Analog to Digital Converter Control Interface
<!-- BEGIN AUTOGEN from util/mdbook_regression_links.py -->
| Regression | Version | [Stages](https://opentitan.org/book/doc/project_governance/development_stages.html) | Results |
|-|-|-|-|
 [`adc_ctrl`](https://nightly.reports.lowrisc.org/opentitan_weekly_earlgrey/2026_03_08/index.html) | 2.0.0 | D2S, V2S | <img src="https://img.shields.io/badge/Tests_Running-920-blue"> <img src="https://img.shields.io/badge/Tests_Passing-97.17%25-brightgreen"> <img src="https://img.shields.io/badge/Functional_Coverage-91.68%25-brightgreen"> <img src="https://img.shields.io/badge/Code_Coverage-98.74%25-brightgreen"> |

This IP has been taped out in Earl Grey 1.0.0. The corresponding documentation and regression results can be found [here](https://opentitan.org/earlgrey_1.0.0/book/hw/ip/adc_ctrl/index.html).
<!-- END AUTOGEN -->

# Overview

This document specifies the ADC controller IP functionality.
This IP block implements control and filter logic for an analog block that implements a dual ADC.
This module conforms to the [Comportable guideline for peripheral functionality.](../../../doc/contributing/hw/comportability/README.md)
See that document for integration overview within the broader top level system.

## Features

The IP block implements the following features:

- Register interface to dual ADC analog block
- Support for 2 ADC channels
- Support for 8 filters on the values from the channels
- Support ADCs with 10-bit output (two reserved bits in CSR)
- Support for debounce timers on the filter output
- Run on a slow always-on clock to enable usage while the device is sleeping
- Low power periodic scan mode for monitoring ADC channels

## Description

The ADC controller is a simple front-end to an analog block that allows filtering and debouncing of the analog signals.

## Compatibility

The ADC controller programming interface is not based on any existing interface.
