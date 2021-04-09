---
title: "Padctrl Technical Specification"
---


# Overview

This document specifies the functionality of the pad control block.
This module is a peripheral on the chip interconnect bus, and thus follows the
[OpenTitan guideline for peripheral device functionality.]({{< relref "doc/rm/comportability_specification" >}}).
See that document for integration overview within the broader OpenTitan top level system.


## Features

- Programmable control of chip pin input/output inversion

- Programmable control of chip pin output locking enable

- Programmable control of chip pin output drive strength, pull up, pull down and virtual open drain

## Description

The `padctrl` module instantiates all chip pads and provides a software accessible register file to control pad attributes such as pull-up, pull-down, virtual open-drain, drive-strength, keeper and input/output inversion.
The `padctrl` module supports a comprehensive set of pin attributes, but it is permissible that some of them may not be supported by the underlying pad implementation.
For example, certain ASIC libraries may not provide open-drain outputs, and FPGAs typically do not allow all of these attributes to be programmed dynamically at runtime.

Note that static pin attributes for FPGAs are currently not covered in this specification.


# Theory of Operations


## Block Diagram

Even though the pad control IP is referred to as one IP, it is logically split into two modules that are instantiated on the top-level and the chip-level respectively, as shown in the block diagram below.
The top-level module `padctrl` contains the CSRs that are accessible via the TL-UL interface, while the chip-level module `padring` instantiates the bidirectional pads and connects the physical pin attributes.

![Padctrl Block Diagram](padctrl_block_diagram.svg)

The chip level `padctrl` module provides two sets of parametric IO arrays prefixed with `mio*` and `dio*`.
Both sets are functionally equivalent, but are meant to be used with either multiplexed or dedicated IOs as the naming suggests.
I.e., the `mio*` pads can be connected to the `pinmux` module ([see spec]({{< relref "." >}})) in order to provide as much IO flexibility as possible to the software running on the device.
The `dio*` pads on the other hand are to be connected to peripherals that require dedicated ownership of the pads.
Examples that fall into the latter category are a high-speed SPI peripherals or a UART device that should always be connected for debugging purposes.

The implementation of the pad wrapper can be technology dependent, but the interface must follow the specification detailed in this document (see following sections).
This ensures that the pad instance compatible with the target technology can be selected during the RTL build flow by just including the right pad wrapper IP, without having to regenerate parts of the `padctrl` code.

Note that the chip-level `padctrl` module also contains the pads for clock and reset, but these have no associated runtime configurable pad attributes.

## Hardware Interfaces


### Parameters

The following table lists the main parameters used throughout the `padctrl` design.
Note that the `padctrl` modules are generated based on the system configuration, and hence these parameters are placed into a package as "localparams".

Localparam     | Default (Min, Max)    | Description
---------------|-----------------------|---------------
NMioPads       | 4 (1, -)              | Number of muxed output pads.
NDioPads       | 16 (1, -)             | Number of dedicated output pads.
AttrDw         | 10 (9, -)             | Width of the pad attribute vector.

### Additional IOs

The table below lists additional `padctrl` signals.
The number of IOs is parametric, and hence the signals are stacked in packed arrays.

Signal                                 | Direction        | Type                | Description
---------------------------------------|------------------|---------------------|---------------
`mio_attr_o[NMioPads-1:0][AttrDw-1:0]` | `output`         | packed `logic`      | Packed array containing the pad attributes of all muxed IOs.
`dio_attr_o[NDioPads-1:0][AttrDw-1:0]` | `output`         | packed `logic`      | Packed array containing the pad attributes of all dedicated IOs.

The table below lists the `padring` signals.
The number of IOs is parametric, and hence the signals are stacked in packed arrays.

Signal                                 | Direction        | Type                | Description
---------------------------------------|------------------|---------------------|---------------
`clk_pad_i`                            | `input`          | `wire`              | Clock pad input.
`rst_pad_ni`                           | `input`          | `wire`              | Reset pad input.
`mio_pad_io[NMioPads-1:0]`             | `inout`          | packed `wire`       | Bidirectional IOs of the muxed IO pads.
`dio_pad_io[NDioPads-1:0]`             | `inout`          | packed `wire`       | Bidirectional IOs of the dedicated IO pads.
`clk_o`                                | `output`         | `logic`             | Clock output (to clocking infrastructure).
`rst_no`                               | `output`         | `logic`             | Reset output (to reset infrastructure).
`mio_attr_i[NMioPads-1:0][AttrDw-1:0]` | `input`          | packed `logic`      | Packed array containing the pad attributes of all muxed IOs.
`dio_attr_i[NDioPads-1:0][AttrDw-1:0]` | `input`          | packed `logic`      | Packed array containing the pad attributes of all dedicated IOs.
`mio_in_o[NMioPads-1:0]`               | `output`         | packed `logic`      | Input data signals of muxed IOs.
`dio_in_o[NDioPads-1:0]`               | `output`         | packed `logic`      | Input data signals of dedicated IOs.
`mio_out_i[NMioPads-1:0]`              | `input`          | packed `logic`      | Output data signal of muxed IOs.
`dio_out_i[NDioPads-1:0]`              | `input`          | packed `logic`      | Output data signal of dedicated IOs.
`mio_oe_i[NMioPads-1:0]`               | `input`          | packed `logic`      | Output data enable of muxed IOs.
`dio_oe_i[NDioPads-1:0]`               | `input`          | packed `logic`      | Output data enable of dedicated IOs.


## Design Details

### Generic Pad Wrapper

<center>
<img src="generic_pad_wrapper.svg" width="50%">
</center>

The generic pad wrapper is intended to abstract away implementation differences between the target technologies by providing a generic interface that is compatible with the `padring` module.
It is the task of the RTL build flow to select the appropriate pad wrapper implementation.

A specific implementation of a pad wrapper may choose to instantiate a technology primitive (as it is common in ASIC flows), or it may choose to model the functionality behaviorally such that it can be inferred by the technology mapping tool (e.g., in the case of an FPGA target).
It is permissible to omit the implementation of all IO attributes except input/output inversion.

The generic pad wrapper must expose the following IOs and parameters, even if they are not connected internally.
In particular, the pad attribute struct `attr_i` must contain all fields listed below, even if not all attributes are supported (it is permissible to just leave them unconnected in the pad wrapper implementation).

Parameter      | Default    | Description
---------------|------------|-----------------------------------------------------
`PadType`      | `BidirStd` | Pad variant to be instantiated (technology-specific)
`ScanRole`     | `NoScan`   | Scan role, can be `NoScan`, `ScanIn` or `ScanOut`

Note that `PadType` is a technology-specific parameter.
The generic pad wrapper only implements variant `BidirStd`, but for other target technologies, this parameter can be used to select among a variety of different pad flavors.

The `ScanRole` parameter determines the behavior when scanmode is enabled.
Depending on whether a given pad acts as a scan input or output, certain pad attributes and functionalities need to be bypassed.
This parameter is typically only relevant for ASIC targets and therefore not modeled in the generic pad model.

Also note that the pad wrapper may implement a "virtual" open drain termination, where standard bidirectional pads are employed, but instead of driving the output high for a logic 1 the pad is put into tristate mode.

Signal               | Direction  | Type        | Description
---------------------|------------|-------------|-----------------------------------------------
`clk_scan_i`         | `input`    | `logic`     | Scan clock of the pad
`scanmode_i`         | `input`    | `logic`     | Scan mode enable of the pad
`pok_i`              | `input`    | `pad_pok_t` | Technology-specific power sequencing signals
`inout_io`           | `inout`    | `wire`      | Bidirectional inout of the pad
`in_o`               | `output`   | `logic`     | Input data signal
`in_raw_o`           | `output`   | `logic`     | Un-inverted input data signal
`out_i`              | `input`    | `logic`     | Output data signal
`oe_i`               | `input`    | `logic`     | Output data enable
`attr_i[0]`          | `input`    | `logic`     | Input/output inversion
`attr_i[1]`          | `input`    | `logic`     | Virtual open drain enable
`attr_i[2]`          | `input`    | `logic`     | Pull enable
`attr_i[3]`          | `input`    | `logic`     | Pull select (0: pull down, 1: pull up)
`attr_i[4]`          | `input`    | `logic`     | Keeper enable
`attr_i[5]`          | `input`    | `logic`     | Schmitt trigger enable
`attr_i[6]`          | `input`    | `logic`     | Open drain enable enable
`attr_i[8:7]`        | `input`    | `logic`     | Slew rate (0x0: slowest, 0x3: fastest)
`attr_i[12:9]`       | `input`    | `logic`     | Drive strength (0x0: weakest, 0xf: strongest)

# Programmers Guide

Software should determine and program the `padctrl` pin attributes at startup, or reprogram it when the functionality requirements change at runtime.

This can be achieved by writing to the {{< regref "MIO_PADS" >}} and {{< regref "DIO_PADS" >}} registers.
Note that the IO attributes should be configured before enabling any driving modules such as the `pinmux` in order to avoid undesired electrical behavior and/or contention at the pads.

The padctrl configuration can be locked down by writing a 0 to register {{< regref "REGEN" >}}.
The configuration can then not be altered anymore unless the system is reset.
One possible future enhancement is to individually lock each register instead of locking them all at once.

Note that the register description given in the next section is an example that has been generated with the default parameterization, and the layout may change once reparameterized.
The following pad attributes are supported by this register layout by default:

ATTR Bits | Description                                   | Access
----------|-----------------------------------------------|---------
0         | Input/output inversion                        | RW
1         | Open drain enable                             | RW
2         | Pull enable                                   | WARL
3         | Pull select (0: down, 1: up)                  | WARL
4         | Keeper enable                                 | WARL
5         | Schmitt trigger enable                        | WARL
6         | Open drain enable enable                      | WARL
8:7       | Slew rate (0x0: slowest, 0x3: fastest)        | WARL
12:9      | Drive strength (0x0: weakest, 0xf: strongest) | WARL

Since some of the pad attributes may not be implemented, software can probe this capability by writing the CSRs and read them back to determine whether the value was legal.
This behavior is also referred to as "writes-any-reads-legal" or "WARL" in the RISC-V world.

It should be noted that not all pads support all slew rate or drive bits.
For example, certain pads may only support two drive strength bits (indices [10:9]).
The WARL behavior of the corresponding attribute CSRs reflects that accordingly.

## Register Table
