# Analog to Digital Converter Control Interface

[`adc_ctrl`](https://reports.opentitan.org/hw/ip/adc_ctrl/dv/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/adc_ctrl/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/adc_ctrl/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/adc_ctrl/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/adc_ctrl/code.svg)

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
