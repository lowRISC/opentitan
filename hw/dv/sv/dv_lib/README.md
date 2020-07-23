---
title: "DV Library Classes"
---

# DV library classes

## Overview
The DV library classes form the base layer / framework for constructing UVM
testbenches. These classes provide features (settings, methods, hooks and other
constructs used in verification) that are generic enough to be reused across
all testbenches.

In this doc, we will capture some of the most salient / frequently used features
in extended classes. These classes are being updated frequently. So, for a more
detailed understanding, please read the class definitions directly.

The DV library classes fall into 3 categories - UVM RAL (register abstraction
layer), UVM agent, and UVM environment extensions.

### UVM RAL extensions
The RAL model generated using the [reggen]({{< relref "util/reggen/README.md" >}}) tool
extend from these classes. These themselves extend from the corresponding RAL
classes provided in UVM.

#### `dv_base_reg_field`
Currently, this class does not provide any additional features. One of the
features planned for future is setting exclusion tags at the field level for the
CSR suite of tests that will be extracted automatically from the Hjson-based
IP CSR specification.

#### `dv_base_reg`
This class provides the following functions to support verification:
* `gen_n_used_bits()`: This function returns the actual number of bits used in
  the CSR (sum of all available field widths).
* `get_msb_pos()`: This function returns the MSB bit position of all available
  fields. CSR either ends at this bit (`BUS_DW` - 1) or has reserved / invalid
  bits beyond this bit.

#### `dv_base_reg_block`
* ` build(uvm_reg_addr_t base_addr)`: This function is implemented as a pseudo
  pure virtual function (returns a fatal error if called directly). It is used
  for building the complete RAL model. For a polymorphic approach, the DV user
  can use this class handle to create the extended (IP specific) class instance
  and call this function to build the actual RAL model. This is exactly how it
  is done in [dv_base_env_cfg](#dv_base_env_cfg).

#### `dv_base_reg_map`
Currently, this class does not provide any additional features. Having this
extension provides an opportunity to add common features in future.

### UVM Agent extensions
TODO

### UVM Environment extensions
TODO

