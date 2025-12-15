# MEM_XYZ HW IP Technical Specification
[`mem_xyz`]

# Overview
This document specifies MEM_XYZ hardware IP functionality. This module conforms to
the [OpenTitan guideline for peripheral device functionality.](../../../doc/contributing/hw/comportability/README.md)
See that document for integration overview within the broader OpenTitan top level system.

## Features
- <!-- req_mem_xyz_162F begin -->Memory address space is...<!-- req_mem_xyz_162F end -->
- <!-- req_mem_xyz_0882 begin -->It supports read and write commands<!-- req_mem_xyz_0882 end -->
- <!-- req_mem_xyz_24BE begin -->All the address space is read and write accessible<!-- req_mem_xyz_24BE end -->
- Address width is an RTL parameter among:
  - <!-- req_mem_xyz_3A6A begin -->8<!-- req_mem_xyz_3A6A end -->
  - <!-- req_mem_xyz_3A4E begin -->16<!-- req_mem_xyz_3A4E end -->
  - <!-- req_mem_xyz_3637 begin -->32<!-- req_mem_xyz_3637 end -->
- <!-- req_mem_xyz_10B7 begin -->Multiple modes are available: mode_a, mode_b and mode_c<!-- req_mem_xyz_10B7 end -->
