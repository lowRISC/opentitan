---
title: "Primitive Component: Packer FIFO"
---

# Overview

`prim_packer_fifo` is a module that supports three modes of operation: packing,
unpacking, and single depth FIFO modes. Packing mode is where the input
data width is less than the output data width. Unpacking mode is where the input
data width is greater than the output data width. Single depth FIFO is where
the input and output data widths are the same. Because masking options are not
supported, the larger data size must be an even multiple of the smaller size.
The controls for this module are modeled after the `prim_fifo_sync` module,
both in name and functional behavior.
It is one of a set of shared primitive modules
available for use within OpenTitan as referred to in the Comportability
Specification section on shared primitives.

## Parameters

Name | type | Description
-----|------|-------------
InW  | int  | Input data width
OutW | int  | Output data width

## Signal Interfaces

Name         | In/Out | Description
-------------|--------|-------------
clk_i        | input  | Input clock
rst_ni       | input  | Input reset, negative active
clr_i        | input  | Input clear, clears all internal flops.
wvalid_i     | input  | Writes data into the first available position.
wdata_i[InW] | input  | Input data.
wready_o     | output | Indicates if prim_packer_fifo is able to accept data.
rvalid_o     | output | Indicates if output data is valid.
rdata_o[OutW]| output | Output data.
rready_i     | input  | Output data is popped from the FIFO.
depth_o      | output | Indicates the fullness of the FIFO.

# Theory of Opeations

```code
           /----------\
wvalid_i   |          |      rvalid_o
---------->|          |--------------->
wdata_i    |   Flop   |      rdata_o
=====/====>|   FIFO   |=======/=======>
  [InW]    |          |      [OutW]
           |          |      depth_o    
           |          |--------------->   
wready_o   |          |      rready_i
<----------|          |<---------------
           |          |
           \----------/
```

In pack mode, `prim_packer_fifo` accepts `InW` bits of data. On a `wvalid_i`/
`wready_o` handshake, `wdata_i` is stored to internal registers and accumulated
until `OutW` data has been gathered. Once the FIFO is full, a single pop (when
rvalid_o and rready_i are coincident), will clear the data and depth values on
the next clock cycle. The complimentary flow occurs when the`prim_packer_fifo`
module is in unpack mode.

The internal register size is the greate of `InW` and `OutW` bits.
Timing diagrams are shown in the header of the `prim_packer_fifo` module.

