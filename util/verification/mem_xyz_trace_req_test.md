# MEM_XYZ HW IP Technical Specification

[`mem_xyz`](https://reports.opentitan.org/hw/ip/mem_xyz/dv/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/mem_xyz/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/mem_xyz/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/mem_xyz/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/mem_xyz/code.svg)

# Overview

This document specifies MEM_XYZ hardware IP functionality. This module conforms to
the [OpenTitan guideline for peripheral device functionality.](../../../doc/contributing/hw/comportability/README.md)
See that document for integration overview within the broader OpenTitan top level system.


## Features

- Memory address space is...<!-- req_mem_xyz_162F -->
- It supports read and write commands<!-- req_mem_xyz_0882 -->
- All the address space is read and write accessible<!-- req_mem_xyz_24BE -->
- Address width is an RTL parameter among:
  - 8<!-- req_mem_xyz_3A6A -->
  - 16<!-- req_mem_xyz_3A4E -->
  - 32<!-- req_mem_xyz_3637 -->
- Multiple modes are available: mode_a, mode_b and mode_c<!-- req_mem_xyz_10B7 -->
