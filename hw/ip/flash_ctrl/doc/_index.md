---
title: "Flash Controller HWIP Technical Specification"
---

# Overview

This document describes the flash hardware functionality.
The flash hardware is broken down into 3 major components
* Open source flash controllers
* Closed source vendor flash wrapper
* Closed source vendor flash module

A breakdown of the 3 can be seen below
![Flash High Level Boundaries](flash_boundaries.svg)


This open source flash controller is divided into two partitions.

* Flash protocol controller
* Flash physical controller

The remaining document focuses primarily on the function of these blocks.

This module conforms to the [Comportable guideline for peripheral functionality.]({{< relref "doc/rm/comportability_specification" >}})
See that document for integration overview within the broader top level system.

## Features

### Flash Protocol Controller Features
The flash protocol controller interfaces with software and other hardware components in the system (such as life cycle and key manager).
Regardless of the flash size underneath, the flash controller maintains the same data resolution as the bus and processor (default 4B).
The flash physical controller (see section below) is then responsible for bridging that gap.

The protocol controller currently supports the following features:

*  Controller initiated read, program and erase of flash.
   *  Erase can be either of a page, or an entire bank.
*  Support for differentiation between informational and data flash partitions.
*  Parameterized support for burst program, up to 64B
   *  Longer programs are supported, however the protocol controller will directly back-pressure the bus.
*  Flash memory protection at page boundaries
*  Features to be added if required
   *  Program verification
      *  may not be required if flash memory supports alternative mechanisms of verification.
   *  Erase verification
      *  may not be required if flash memory supports alternative mechanisms of verification.
   *  Flash redundant pages
      *  Flash may contain additional pages used to remap broken pages for yield recovery.
      *  The storage, loading and security of redundant pages may also be implemented in the physical controller or flash memory.

Features to be implemented

*  Enhanced memory protection
*  Life cycle feature support
*  Key manager feature support

### Flash Physical Controller Features

The flash physical controller wraps the actual flash memory and translates both host and controller initiated requests into low level flash transactions.

The physical controller supports the following features
*  Multiple banks of flash memory
*  For each flash bank, parameterized support for number of flash pages (default to 256)
*  For each flash page, parameterized support for number of words and word size (default to 128 words of 8-bytes each)
*  Data and informational paritions within each bank of flash memory
*  Arbitration between host requests and controller requests at the bank level
   *  Host requests are always favored, however the controller priority can escalate if it repeatedly loses arbitration
   *  Since banks are arbitrated independently, where transactions may take different amounts of times to complete, the physical controller is also responsible for ensuring in-order response to both the controller and host.
*  Flash read stage
   *  Each bank maintains a parameterizable number of read buffers in front of the flash memory
   *  The read buffers behave as miniature read-only-caches to store flash data when flash words are greater than bus words.
*  Flash program stage
   *  Flash data work packing when flash word size is an integer multiple of bus word size.

Features to be implemented

*  Flash scrambling
*  Flash ECC


# Theory of Operation

## Block Diagram

### Flash Protocol Controller

The Flash Protocol Controller sits between the host software interface and the flash physical controller, which contains the physical flash.
Its primary function is to translate software requests into a high level protocol for the actual flash block.
Importantly, the flash protocol controller is not responsible for the detailed timing and waveform control of the flash.
Instead, it maintains FIFOs / interrupts for the software to process data, as well as high level abstraction of region protection controls.

### Flash Physical Controller

The Flash Physical Controller is the wrapper module that contains the actual vendor flash memory instantiation.
It is responsible for arbitrating high level protocol commands (such as read, program, erase) as well as any additional security and reliability features.
The contained vendor wrapper module is then responsible for converting high level commands into low level signaling and timing specific to a particular flash vendor.
The vendor wrapper module is also responsible for any BIST, redundancy handling, remapping features or custom configurations required for the flash.

The diagram below summarizes the high level breakdown.

![Flash High Level Abstraction](flash_abstraction.svg)

## Hardware Interfaces

{{< hwcfg "hw/ip/flash_ctrl/data/flash_ctrl.hjson" >}}

### Signals

In addition to the interrupts and bus signals, the tables below lists the flash protocol controller I/Os.

Signal                  | Direction | Description
------------------------|-----------|---------------
`flash_i`               | `input`   | Inputs from physical controller, connects to `flash_ctrl_o` of physical controller
`flash_o`               | `output`  | Outputs to physical controller, connects to `flash_ctrl_i` of physical controller

Each of `flash_i` and `flash_o` is a struct that packs together additional signals, as shown below

| Signal          | Source               | Destination         | Description
| --------------  | ---------------------| ------------------- | -------------------------------------------------------
| `req`           | protocol controller  | physical controller | Protocol controller initiated transaction
| `addr`          | protocol controller  | physical controller | Protocol controller initiated transaction address
| `rd`            | protocol controller  | physical controller | Protocol controller initiated read
| `prog`          | protocol controller  | physical controller | Protocol controller initiated program
| `pg_erase`      | protocol controller  | physical controller | Protocol controller initiated page erase
| `prog_data`     | protocol controller  | physical controller | Protocol controller initiated program data, 1 flash word wide
| `bk_erase`      | protocol controller  | physical controller | Protocol controller initiated bank erase
| `rd_done`       | physical controller  | protocol controller | Physical controller read done
| `prog_done`     | physical controller  | protocol controller | Physical controller program done
| `erase_done`    | physical controller  | protocol controller | Physical controller erase done
| `init_busy`     | physical controller  | protocol controller | Physical controller reset release initialization in progress
| `rd_data`       | physical controller  | protocol controller | Physical Controller read data, 1 flash word wide

The physical controller IOs are listed and described below.

| Signal            | Direction | Description
| ----------------- | ----------| -------
| `host_req_i`      | input     | Host initiated direct read, should always be highest priority.  Host is only able to perform direct reads
| `host_addr_i`     | input     | Address of host initiated direct read
| `host_req_rdy_o`  | output    | Host request ready, '1' implies transaction has been accepted, but not necessarily finished
| `host_req_done_o` | output    | Host request completed
| `host_rdata_o`    | output    | Host read data, 1 flash word wide
| `flash_ctrl_i`    | input     | Inputs from protocol controller, connects to `flash_o` of protocol controller
| `flash_ctrl_o`    | output    | Outputs to protocol controller, connects to `flash_i` of protcol controller

## Design Detials

### Flash Protocol Controller Description

The flash protocol controller uses a simple FIFO interface to communicate between the software and flash physical controller.
There is a read fifo for read operations, and a program fifo for program operations.
Note, this means flash can be read both through the controller and the main bus interface.
This may prove useful if the controller wishes to allocate specific regions to HW FSMs only, but is not a necessary feature.

When software initiates a read transaction of a programmable number of flash words, the flash controller will fill up the read FIFO for software to consume.
Likewise, when software initiates a program transaction, software will fill up the program FIFO for the controller to consume.

The controller is designed such that the overall number of words in a transaction can significantly exceed the FIFO depth.
In the case of read, once the FIFO is full, the controller will cease writing more entries and wait for software to consume the contents (an interrupt will be triggered to the software to alert it to such an event).
In the case of program, the controller will stop writing to flash once all existing data is consumed - it will likewise trigger an interrupt to software to prepare more data.
See detailed steps in theory of operation.
The following is a diagram of the controller construction as well as its over connectivity with the flash module.

![Flash Protocol Controller](flash_protocol_controller.svg)


### Host Read

Unlike controller initiated reads, host reads have separate rdy / done signals to ensure transactions can be properly pipelined.
As host reads are usually tied to host execution upstream, additional latency can severely harm performance and is not desired.
The expected waveform from the perspective of the physical controller is shown below.

{{< wavejson >}}
{signal: [
  {name: 'clk_i',           wave: 'p..............'},
  {name: 'rst_ni',          wave: '0.1............'},
  {name: 'host_req_i',      wave: '0..10.1...0....'},
  {name: 'host_addr_i',     wave: 'x..3x.3.33x....', data: ['Adr0', 'Adr1', 'Adr2', 'Adr3']},
  {name: 'host_req_rdy_o',  wave: '1...0..1.......'},
  {name: 'host_req_done_o', wave: '0...10..1110...'},
  {name: 'host_rdata_o',    wave: 'x...4x..444x...',data: ['Dat0', 'Dat1', 'Dat2', 'Dat3']},
]}
{{< /wavejson >}}

The `host_req_done_o` is always single cycle pulsed and upstream logic is expected to always accept and correctly handle the return.
The same cycle the return data is posted a new command / address can be accepted.
While the example shows flash reads completing in back to back cycles, this is typically not the case.

### Controller Read

Unlike host reads, controller reads are not as performance critical and do not have command / data pipeline requirements.
Instead, the protocol controller will hold the read request and address lines until the done is seen.
Once the done is seen, the controller then transitions to the next read operation.
The expected waveform from the perspective of the physical controller is shown below.

{{< wavejson >}}
{signal: [
  {name: 'clk_i',                 wave: 'p..............'},
  {name: 'rst_ni',                wave: '0.1............'},
  {name: 'flash_ctrl_i.req',      wave: '0..1.....0.....'},
  {name: 'flash_ctrl_i.addr',     wave: 'x..3..3..x.3..x', data: ['Adr0', 'Adr1', 'Adr2']},
  {name: 'flash_ctrl_i.rd',       wave: '0..1.....0.1..0'},
  {name: 'flash_ctrl_o.rd_done',  wave: '0....10.10...10'},
  {name: 'flash_ctrl_o.rdata',    wave: 'x....4x.4x...4x', data: ['Dat0', 'Dat1', 'Dat2']},
]}
{{< /wavejson >}}

### Controller Program

Program behavior is similar to reads.
The protocol controller will hold the request, address and data lines until the programming is complete.
The expected waveform from the perspective of the physical controller is shown below.

{{< wavejson >}}
{signal: [
  {name: 'clk_i',                  wave: 'p..............'},
  {name: 'rst_ni',                 wave: '0.1............'},
  {name: 'flash_ctrl_i.req',       wave: '0..1.....0.....'},
  {name: 'flash_ctrl_i.addr',      wave: 'x..3..3..x.3..x', data: ['Adr0', 'Adr1', 'Adr2']},
  {name: 'flash_ctrl_i.prog',      wave: '0..1.....0.1..0'},
  {name: 'flash_ctrl_o.prog_data', wave: 'x..4..4..x.4..x', data: ['Dat0', 'Dat1', 'Dat2']},
  {name: 'flash_ctrl_o.prog_done', wave: '0....10.10...10'},
]}
{{< /wavejson >}}

# Programmers Guide

## Issuing a Controller Read

To issue a flash read, the programmer must
*  Specify the address of the first flash word to read
*  Specify the number of total flash words to read, beginning at the supplied address
*  Specify the operation to be 'READ' type
*  Set the 'START' bit for the operation to begin

The above fields can be set in the {{< regref "CONTROL" >}} and {{< regref "ADDR" >}} registers.
See [library code](https://github.com/lowRISC/opentitan/blob/master/sw/device/lib/flash_ctrl.c) for implementation.

It is acceptable for total number of flash words to be significantly greater than the depth of the read FIFO.
In this situation, the read FIFO will fill up (or hit programmable fill value), pause the flash read and trigger an interrupt to software.
Once there is space inside the FIFO, the controller will resume reading until the appropriate number of words have been read.
Once the total count has been reached, the flash controller will post OP_DONE in the {{< regref "OP_STATUS" >}} register.

## Issuing a Controller Program

To program flash, the same procedure as read is followed.
However, instead of setting the {{< regref "CONTROL" >}} register for read operation, a program operation is selected instead.
Software will then fill the program FIFO and wait for the controller to consume this data.
Similar to the read case, the controller will automatically stall when there is insufficient data in the FIFO.
When all desired words have been programmed, the controller will post OP_DONE in the {{< regref "OP_STATUS" >}} register.

## Register Table

The flash protocol controller maintains two separate access windows for the FIFO.
It is implemented this way because the access window supports transaction back-pressure should the FIFO become full (in case of write) or empty (in case of read).

{{< registers "hw/ip/flash_ctrl/data/flash_ctrl.hjson" >}}
