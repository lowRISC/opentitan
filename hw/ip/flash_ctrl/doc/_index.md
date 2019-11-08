---
title: "Flash Controller HWIP Technical Specification"
---

# Overview

This document specifies flash hardware IP functionality.
As the final feature set will largely depend on how similar flash IPs are, it is at the moment unclear where the open-source / proprietary boundaries should lie.
This document thus makes a best effort estimate as to what that boundary should be and breaks the functionality down accordingly.

This document assumes flash functionality shall be divided into two partitions.

* Flash protocol controller
* Flash physical controller

This module conforms to the [Comportable guideline for peripheral functionality.]({{< relref "doc/rm/comportability_specification" >}})
See that document for integration overview within the broader top level system.

## Features

### Flash Protocol Controller Features

*  Support controller initiated read, program and erase of flash.
   *  Erase can be either of a page, or an entire bank.
*  Parameterized support for number of flash banks (default to 2)
*  For each flash bank, parameterized support for number of flash pages (default to 256)
*  For each flash page, parameterized support for number of words and word size (default to 256 words of 4-bytes each)
*  Parameterized support for burst writes, up to 64B
   *  Controller currently does not support page boundary checks; it is thus legal for software to burst write across a page boundary
*  Features to be added if required
   *  Parameterizable data width
   *  Program verification
      *  may not be required if flash physical controller supports alternative mechanisms of verification.
   *  Erase verification
      *  may not be required if flash physical controller supports alternative mechanisms of verification.
   *  Parity / ECC support on a per flash page granularity
      *  may not be required depending on flash reliability or overall system security strategy.
   *  Flash redundant pages
      *  Flash may contain additional pages used to remap broken pages for yield recovery.
      *  The storage, loading and security of redundant pages may also be implemented in the physical controller.
   *  Flash information pages
      *  Flash may contain additional pages outside of the data banks to hold manufacturing information (such as wafer location).
      *  Extra logic may not be required if flash information pages is treated as just a separate address.

### Flash Physical Controller Features

As the flash physical controller is highly dependent on flash memory selected, the default flash physical controller simply emulates real flash behavior with on-chip memories.
The goal of the emulated flash is to provide software developers with a reasonable representation of a well-behaving flash operating under nominal conditions.

Below are the emulated properties
*  Flash reset to all 1's
*  Writing of a word will take 50 (parameterizable) clock cycles
*  Erasing of a page will take 200 (parameterizable) clock cycles
*  Erasing of a bank will take 2000 (parameterizable) clock cycles
*  A bit, once written to 0, cannot be written back to 1 until an erase operation has been performed
*  Support for simultaneous controller (read / program / erase) and host (read) operations.
   *  Host operations are always prioritized unless controller operation is already ongoing.
*  The arbitration resolution is done at the bank level
   *  If a bank is busy with an operation, a new operation can be issued to a different bank in parallel.
   *  If a bank is busy with an operation, a new operation issued to the same bank will block until the operation completes.


The flash physical controller does NOT emulate the following properties

*  Flash lifetime
   *  Typically flash memory has an upward limit of 100K+ program / erase cycles.
*  Flash line program disturb
   *  Typically flash memory has limits on the number of program accesses to a single memory line (2 ~ 16) before erase is required,
*  Flash power loss corruption
   *  Typically flash memory has strict requirements how power loss should be handled to prevent flash failure.
*  Dedicated flash power supplies

Depending on need, it may be necessary to add controller logic to perform the following functions
*  Flash BIST
   * Technology dependent mechanism to perform flash self test during manufacuring.
*  Flash custom controls
   * There may be additional tuning controls for a specific flash technology.
*  Power loss handling
   * Specific power loss handling if power is lost during an erase or program operation.
*  Additional security lockdown
   * As the physical controller represents the final connecting logic to the actual flash memory, additional security considerations may be required to ensure backdoor access paths do not exist.


# Theory of Operation

## Block Diagram

### Flash Protocol Controller

The Flash Protocol Controller sits between the host software interface and the physical flash.
Its primary function is to translate software requests into a high level protocol for the actual flash block.
Importantly, the flash protocol controller shall not be responsible for the detailed timing and waveform control of the flash.
Instead, it shall maintain FIFOs / interrupts for the software to process data.

### Flash Physical Controller

The Flash Physical Controller is the wrapper module that contains the actual flash memory instantiation.
It is responsible for converting high level protocol commands (such as read, program, erase) into low level signaling and timing specific to a particular flash IP.
It is also responsible for any BIST, redundancy handling, remapping features or custom configurations required for the flash memory.

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
