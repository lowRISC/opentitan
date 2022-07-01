---
title: "Earl Grey Top Level Specification"
---

# Overview

<img src="earlgrey.png" align="right" alt="Earl Grey logo" width=200 title="Earl Grey" hspace="20"/>

This document specifies the top level functionality of the "Earl Grey" chip (`top_earlgrey`).

## Features

- RISC-V microprocessor ("Ibex") and associated JTAG IO. Related features:
  - DM (debug module)
  - PLIC (platform level interrupt controller)
  - U/M execution modes (user/machine)
  - Enhanced Physical Memory Protection (ePMP)
  - Security features:
    - Dual core lockstep configuration
    - Data independent timing
    - Dummy instruction insertion
    - Bus and register file integrity
    - Hardened PC
- Memory
  - 1024kB eFlash
  - 128kB SRAM
  - 4KB Always ON (AON) retention SRAM
  - 32kB ROM
  - All memories support scrambling and integrity checks.
- Security peripherals
  - Flash controller
  - AES
  - SHA2-256/HMAC
  - SHA3-KMAC
  - CSRNG
  - Big Number Accelerator (OTBN)
  - Key Manager with DICE support
  - Alert handler
  - Digital wrapper for entropy source
- IO peripherals
  - x32 multiplexable IO pads with pin multiplexing unit and pad control
  - GPIO (using multiplexable IO)
  - x4 UART (using multiplexable IO)
  - x3 I2C with support for host and device modes (using multiplexable IO)
  - SPI device (using fixed IO) with the following modes of operation: TPM, generic, flash and passthrough
  - x2 SPI host
- Other peripherals
  - Fixed-frequency timer
  - Always ON (AON) timer
  - Pulse-Width Modulator (PWM)
  - Pattern Generator
- Clock and reset IO and management
- Software
  - Boot ROM implementing code secure boot and chip configuration
  - Bare metal applications and validation tests

## Description

The netlist `top_earlgrey` contains the features listed above, proving basic functionality of the Ibex RISC-V processor core on an FPGA development environment, with a suite of peripherals and memories.

The code for Ibex is developed in its own [lowRISC repo](http://github.com/lowrisc/ibex), and is [*vendored in*]({{< relref "doc/ug/vendor_hw.md" >}}) to this repository.
Surrounding Ibex is a suite of *Comportable* peripherals that follow the [Comportability Guidelines]({{< relref "doc/rm/comportability_specification" >}}) for lowRISC peripheral IP.
Each of these IP has its own specification.
See the table produced in the [hardware documentation page]({{< relref "hw" >}}) for links to those specifications.

# Theory of Operations

## Block Diagram

The block diagram of `top_earlgrey` (the auto-generated module) is shown below.

**TODO: Top level diagram has pending updates.**

![Top Level Block Diagram](top_earlgrey_block_diagram.svg)

In this diagram, the instantiation of the Ibex processor and all of the memories and comportable IPs are shown.
The IO shown at this level are the internal signals between the IP and the pads instantiated at the target top level netlist.

## Design Details

This section provides some details for the processor and the peripherals.
See their representative specifications for more information.
This section also contains a brief overview of some of the features of the final product.

### Clocking and Reset

In the current version of the chip, clock and reset come from outside the device.
Eventually these will be generated internally to reduce risk of security attack, but internal clock generation is not implemented at this time.
The clock pin is `IO_CLK` and all of the design is synchronous to this one clock.
(Exceptions are peripheral IO that might be synchronized to a local peripheral clock like JTAG TCK or SPI device clock).

Deassertion of the active low reset pin `IO_RST_N` causes the processor to come out of reset and begin executing code at its reset vector.
The reset vector begins in ROM, whose job is to validate code in the emulated e-flash before jumping to it.
The assumption is that the code has been instantiated into the e-flash before reset is released.
This can be done with JTAG commands (see that section), through virtual assignment in verification, or through the `spi_device` peripheral.
Resets throughout the design are asynchronous active low as per the Comportability specification.
Other resets may be generated internally via the alert responder, watchdog timer, etc., and other resets for subunits may be disseminated.
These will be detailed in this section over time.

### System Reset Handling and Flash

Since `top_earlgrey` contains flash, it is important to examine the memory's relationship with resets.

For flash, resets that occur during a stateful operation (program or erase) must be carefully handled to ensure the flash memory is not damaged.
There are three reset scenarios:

* Reset due to external supply lowering.
* Reset due to internal peripheral request.
* Reset due to lower power entry and exit.

#### Reset due to External Supply

Device resets due to supply dropping below a specific threshold are commonly known as "brown-out".
When this occurs, the flash memory must go through specialized sequencing to ensure the cells are not damaged.
This process is handled exclusively between [ast]({{< relref "hw/top_earlgrey/ip/ast/doc" >}})) and the flash.
Please see the [relevant section]({{< relref "hw/top_earlgrey/ip/ast/doc/#main-vcc-power-detection-and-flash-protection" >}}) for more details.

#### Reset due to Internal Request

When the device receives an internal request to reset (for example [aon_timer]({{< relref "hw/ip/aon_timer/doc/#aon-watchdog-timer" >}})), device power is kept on and the flash is directly reset.
It is assumed that the flash device, when powered, will be able to correctly handle such a sequence and properly protect itself.

#### Reset due to Low Power Entry

When the device receives a low power entry request while flash activity is ongoing, the [pwrmgr]({{< relref "hw/ip/pwrmgr/doc/#abort-handling" >}})) is responsible for ensuring the entry request is aborted.


### Main processor (`core_ibex`)

The main processor (`core_ibex`) is a small and efficient, 32-bit, in-order RISC-V core with a 2-stage pipeline that implements the RV32IMC instruction set architecture.
It was initially developed as part of the [PULP platform](https://www.pulp-platform.org) under the name "Zero-riscy" [\[1\]](https://doi.org/10.1109/PATMOS.2017.8106976), and has been contributed to [lowRISC](https://www.lowrisc.org) who maintains it and develops it further.
See the [core_ibex specification](https://ibex-core.readthedocs.io/en/latest/) for more details of the core.
In addition to the standard RISC-V functionality, Ibex implements M (machine) and U (user) mode per the RISC-V standard.
Attached to the Ibex core are a debug module (DM) and interrupt module (PLIC).

#### JTAG / Debug module

One feature available for Earl Grey processor core is debug access.
By interfacing with JTAG pins, logic in the debug module allows the core to enter debug mode (per RISC-V 0.13 debug spec), and gives the design the ability to inject code either into the device - by emulating an instruction - or into memory.
Full details can be found in the [rv_dm specification]({{< relref "hw/ip/rv_dm/doc" >}}).

#### Interrupt Controller

Adjacent to the Ibex core is an interrupt controller that implements the RISC-V PLIC standard.
This accepts a vector of interrupt sources within the device, and assigns leveling and priority to them before sending to the core for handling.
See the details in the [rv_plic specification]({{< relref "../ip_autogen/rv_plic/doc" >}}).

#### Performance

Ibex currently achieves a [CoreMark](https://www.eembc.org/coremark/) per MHz of 2.36 on the earlgrey verilator system.
Performance improvements are ongoing, including the following items being considered:

1. Adding a new ALU to calculate branch targets to remove a cycle of latency on taken conditional branches (currently the single ALU is used to compute the branch condition then the branch target the cycle following if the branch is taken).
2. A 3rd pipeline stage to perform register writeback, this will remove a cycle of latency from all loads and stores and prevent a pipeline stall where a response to a load or store is available the cycle after the request.
3. Implement a single-cycle multiplier.
4. Produce an imprecise exception on an error response to a store allowing Ibex to continue executing past a store without waiting for the response.

The method for including these features, e.g. whether they will be configurable options or not, is still being discussed.

The Ibex documentation has more details on the current pipeline operation, including stall behaviour for each instruction in the [Pipeline Details](https://ibex-core.readthedocs.io/en/latest/03_reference/pipeline_details.html) section.

The CoreMark performance achieved relies in part on single-cycle access to instruction memory.
An instruction cache is planned to help maintain this performance when using flash memory that will likely not have single-cycle access times.

CoreMark was compiled with GCC 9.2.0 with flags: `-march=rv32imc -mabi=ilp32 -mcmodel=medany -mtune=sifive-3-series -O3 -falign-functions=16 -funroll-all-loops -finline-functions -falign-jumps=4 -mstrict-align`

### Memory

The device contains three memory address spaces for instruction and data.

Instruction ROM (32kB) is the target for the Ibex processor after release of external reset.
The ROM contains hard-coded instructions whose purpose is to do a minimal subset of platform checking before checking the next stage of code.
The next stage - a boot loader stored in embedded flash memory - is the first piece of code that is not hard-coded into the silicon of the device, and thus must be signature checked.
The ROM executes this signature check by implementing a RSA-check algorithm on the full contents of the boot loader.
The details of this check will come at a later date.
For verification execute-time reasons, this RSA check will be overridable in the FPGA and verification platforms (details TBD).
This is part of the *Secure Boot Process* that will be detailed in a security section in the future.

Earl Grey contains 1024kB of embedded-flash (e-flash) memory for code storage.
This is intended to house the boot loader mentioned above, as well as the operating system and application that layers on top.
At this time there is no operating system provided; applications are simple proof of concept code to show that the chip can do with a bare-metal framework.

Embedded-flash is the intended technology for a silicon design implementing the full OpenTitan device.
It has interesting and challenging parameters that are unique to the technology that the silicon is implemented in.
Earl Grey, as an FPGA proof of concept, will model these parameters in its emulation of the memory in order to prepare for the replacement with the silicon flash macros that will come.
This includes the read-speeds, the page-sized erase and program interfaces, the two-bank update scheme, and the non-volatile nature of the memory.
Since by definition these details can't be finalized until a silicon technology node is chosen, these can only be emulated in the FPGA environment.
We will choose parameters that are considered roughly equivalent of the state of the art embedded-flash macros on the market today.

Details on how e-flash memory is used by software will be detailed in future Secure Boot Process and Software sections over time.

The intent is for the contents of the embedded flash code to survive FPGA reset as it would as a NVM in silicon.
Loading of the FPGA with initial content, or updating with new content, is described in other software specifications.
The SPI device peripheral is provided as a method to bulk-load e-flash memory.
The processor debug port (via JTAG) is also available for code loading.
See those specifications for more details.

Also included is a 128kB of SRAM available for data storage (stack, heap, etc.) by the Ibex processor.
It is also available for code storage, though that is not its intended purpose.

The base address of the ROM, Flash, and SRAM are given in the address map section later in this document.

### Peripherals

Earl Grey contains a suite of "peripherals", or subservient execution units connected to the Ibex processor by means of a bus interconnect.
Each of these peripherals follows an interface scheme dictated in the [Comportability Specification.]({{< relref "doc/rm/comportability_specification" >}}).
That specification details how the processor communicates with the peripheral (via TLUL interconnect); how the peripheral communicates with the chip IO (via fixed or multiplexable IO); how the peripheral communicates with the processor (interrupts); and how the peripheral communicates security events (via alerts).
See that specification for generic details on this scheme.

#### Chip IO Peripherals

##### Pin Multiplexor (`pinmux`) and Pad Control (`padctrl`)

**TODO: this section needs to be updated to reflect the pinmux/padctrl merger**

The pin multiplexor's purpose is to route between peripherals and the available multiplexable IO (`MIO_00 .. MIO_31`) of the chip.
At this time, the pin multiplexor is provided, but it is not used to its full potential.
In addition, the `padctrl` device manages control or pad attributes like drive strength, technology (OD, OS, etc), pull up, pull down, etc., of the chip's external IO.
At this time, the `padctrl` module is provided, but not yet wired up.
It is notable that there are many differences between an FPGA implementation of Earl Grey and an ASIC version when it comes to pins and pads.
For both, the `pinmux` and `padctrl` are expected to play the same role.
Their effect, however, over things like drive strength and Open Drain technology are highly platform-dependent, and are not finalized at this time.

Both `pinmux` and `padctrl` are themselves peripherals on the TLUL bus, with collections of registers that provide software configurability.
See the [pinmux specification]({{< relref "hw/ip/pinmux/doc" >}}) for how to connect peripheral IO to chip IO and for information on pad control features.

##### UART

The chip contains one UART peripheral that implement single-lane duplex UART functionality.
The outputs and inputs can be configured to any chip IO via the [pinmux]({{< relref "hw/ip/pinmux/doc" >}}).

See the [UART specification]({{< relref "hw/ip/uart/doc" >}}) for more details on this peripheral.

##### GPIO

The chip contains one GPIO peripheral that creates 32 bits of bidrectional communication with the outside world via the pinmux.
Via pinmux any of the 32 pins of GPIO can be connected to any of the 32 MIO chip pins, in any direction.
See the [GPIO specification]({{< relref "hw/ip/gpio/doc" >}}) for more details on this peripheral.
See the [pinmux specification]({{< relref "hw/ip/pinmux/doc" >}}) for how to connect peripheral IO to chip IO.

##### SPI device

**TODO: this section has pending updates**

The SPI device implements Firmware Mode, a feature that provides the ability for external drivers to send firmware upgrade code into a bank of embedded flash memory for in-field firmware updates.
Firmware mode has no addressing, and at the moment no other addressing modes are provided.

See the [SPI device specification]({{< relref "hw/ip/spi_device/doc" >}}) for more details on the Firmware Mode implementation.

##### I2C host

In order to be able to command I2C devices on systems where Earl Grey will be included, I2C host functionality will be required.
This will include standard, full, and fast mode, up to 1Mbaud.
More details of the I2C host module will come in a later specification update.
The pins of the I2C host will be available to connect to any of the multiplexable IO (MIO) of the Earl Grey device.
More than one I2C host module might be instantiated in the top level.

#### Security Peripherals

##### AES

[AES](https://nvlpubs.nist.gov/nistpubs/fips/nist.fips.197.pdf) is the primary [symmetric encryption](https://en.wikipedia.org/wiki/Symmetric-key_algorithm) and decryption mechanism used in OpenTitan protocols.
AES runs with key sizes of 128b, 192b, or 256b.
The module can select encryption or decryption of data that arrives in 16 byte quantities to be encrypted or decrypted using different block cipher modes of operation.
It supports [ECB mode](https://en.wikipedia.org/wiki/Block_cipher_mode_of_operation#ECB), [CBC mode](https://en.wikipedia.org/wiki/Block_cipher_mode_of_operation#CBC), [CFB mode](https://en.wikipedia.org/wiki/Block_cipher_mode_of_operation#CFB), [OFB mode](https://en.wikipedia.org/wiki/Block_cipher_mode_of_operation#OFB) and [CTR mode](https://en.wikipedia.org/wiki/Block_cipher_mode_of_operation#CTR).

The [GCM mode](https://en.wikipedia.org/wiki/Block_cipher_mode_of_operation#GCM) is not implemented in hardware, but can be constructed using AES in counter mode.
The integrity tag calculation can be implemented in Ibex and accelerated via bitmanip instructions.

Details on how to write key and data material into the peripheral, how to initiate encryption and decryption, and how to read out results, are available in the [AES specification]({{< relref "hw/ip/aes/doc" >}}).

##### SHA-256/HMAC

SHA-256 is the primary
[hashing algorithm](https://en.wikipedia.org/wiki/Cryptographic_hash_function) used in OpenTitan protocols.
SHA-256 is a member of the [SHA-2](https://en.wikipedia.org/wiki/SHA-2) family of hashing algorithms, where the digest (or hash output) is of 256b length, regardless of the data size of the input to be hashed.
The data is sent into the SHA peripheral after declaring the beginning of a hash request (effectively zeroing out the internal state to initial conditions), 32b at a time.
Once all data has been sent, the user can indicate the completion of the hash request (with optional partial-word final write).
The peripheral produces the hash result available for register read by the user.
All data transfer is processor-available, i.e. data is passed into the module via register writes.

[HMAC](https://en.wikipedia.org/wiki/HMAC) is a message authentication protocol layered on top of a hashing function (in this case SHA-256), mixing in a secret key for cryptographic purposes.
HMAC is a particular application of appending the secret key in a prescribed manner, twice, around the hashing (via SHA-256) of the message.

Details on how to write key and data material into the peripheral, how to initiate hashing / authentication, and how to read out results, are available in the [SHA/HMAC specification]({{< relref "hw/ip/hmac/doc" >}}).

##### Alert Handler

Alerts, as defined in the [Comportability Specification]({{< relref "doc/rm/comportability_specification" >}}), are defined as security-sensitive interrupts that need to be handled in a timely manner to respond to a security threat.
Unlike standard interrupts, they are not solely handled by software.
Alerts trigger a first-stage request to be handled by software in the standard mode as interrupts, but trigger a second-stage response by the alert handler if software is not able to respond.
This ensures that the underlying concern is guaranteed to be addressed if the processor is busy, wedged, or itself under attack.

Each peripheral has an option to present a list of individual alerts, representing individual threats that require handling.
These alerts are sent in a particular encoding method to the alert handler module, itself a peripheral on the system bus.
See the details of the alert handler specification for more information.

##### TRNG entropy source

Randomness is a critical part of any security chip.
It provides variations in execution that can keep attackers from predicting when the best time is to attack.
It provides secret material used for identity and cryptographic purposes.
It can be seeded into algorithmic computation to obscure sensitive data values.
In short, it is a source of critical functionality that must be designed to be truly random, but also free from attack itself.

Most [TRNG](https://en.wikipedia.org/wiki/Hardware_random_number_generator)s (True Random Number Generators) are analog designs, taking advantage of some physical event or process that is non-deterministic.
Example designs rely on metastability, electronic noise, timing variations, thermal noise, quantum variation, etc.
These are then filtered and sent into a pool of entropy that the device can sample at any time, for whatever purposes are needed.
The creation, filtering, storage, protection, and dissemination of the randomness are all deep topics of intense research in their own right.

The primary interface to the entropy pool is a read request of available random bits.
The TRNG interface can indicate how many bits are available, and then software can read from this pool, if available.
Reading of entropy that is not available should immediately trigger an interrupt or an alert.

Since silicon is required to contain an analog design tied to the final chosen silicon technology process, our FPGA implementation can only approximate the results.
We however fully specify the software interface to the TRNG in a digital wrapper.
In FPGA we emulate the randomness with something akin to a [PRBS](https://en.wikipedia.org/wiki/Pseudorandom_binary_sequence).

#### Other peripherals

##### Timer(s)

Timers are critical for operating systems to ensure guaranteed performance for users.
To some level they are even required by the RISC-V specification.
At this time, one timer is provided, a 64b free running timer with a guaranteed (within a certain percentage) frequency.
A second one acting as a watchdog timer that can be used to backstop the processor in the case of it being unresponsive (usually due to development code that is wedged, rather than for instance due to security attack) will be provided in the future.
The goal is for both of these to be satisfied with the same timer module.

The specification for the timer can be found [here]({{< relref "hw/ip/rv_timer/doc" >}}).

##### Flash Controller

The final peripheral discussed in this release of the netlist is an emulated flash controller.
As mentioned in the memory section, up to 1024kB of emulated embedded flash is available for code and data storage.
The primary read path for this data is in the standard memory address space.
Writes to that address space are ignored, however, since one can not write to flash in a standard way.
Instead, to write to flash, software must interact with the flash controller.

Flash functionality include three primary commands: read, erase, and program.
Read, as mentioned above, is standard, and uses the chip memory address space.
Erase is done at a page level, where the page size is parameterizable in the flash controller.
Upon receiving an erase request, the flash controller wipes all contents of that page, rendering the data in all `1`s state (`0xFFFFFFFF` per word).
Afterwards, software can program individual words to any value.
It is notable that software can continue to attempt to program words even before another erase, but it is not physically possible to return a flash bit back to a `'1'` state without another erase.
So future content is in effect an AND of the current content and the written value.

```
next_value = AND(current_value, write_word)
```

Erase and program are slow.
A typical erase time is measured in milliseconds, program times in microseconds.
The flash controller peripheral in this release approximates those expected times.

Security is also a concern, since secret data can be stored in the flash.
Some memory protection is provided by the flash controller.
For more details see the [flash controller module specification]({{< relref "hw/ip/flash_ctrl/doc" >}}).

### Interconnection

Interconnecting the processor and peripheral and memory units is a bus network built upon the TileLink-Uncached-Light protocol.
See the [OpenTitan bus specification]({{< relref "hw/ip/tlul/doc" >}}) for more details.

#### Topology
`top_earlgrey` has a two-level hierarchy for its bus network.
Close to the CPU is the high-speed cluster, with low access latency.
Farther from the CPU, through a low-speed bridge, is the low-speed cluster, with higher access latency.

#### Performance

The following table describes the typical number of CPU cycles from a transaction's launch to its completion for a device in the specified cluster.
Note that these values assume there is no bus contention.

| Cluster    | CPU Access Latency |
| ---------- | ------------------ |
| High speed | 2 CPU cycles       |
| Low speed  | 18-20 CPU cycles   |


## Memory Map

The base addresses of the memory and peripherals are given in the table below.

The choice of memory, or lack thereof at location 0x0 confers two exclusive benefits:
- If there are no memories at location 0x0, then null pointers will immediately error and be noticed by software (the xbar will fail to decode and route)
- If SRAM is placed at 0, accesses to data located within 2KB of 0x0 can be accomplished with a single instruction and thus reduce code size.

For the purpose of `top_earlgrey`, the first option has been chosen to benefit software development and testing

{{< topLevelDoc "earlgrey" "mmap" >}}

## Hardware Interfaces

### Pinout

{{< topLevelDoc "earlgrey" "pinout" >}}

# RTL Implementation Notes

At this time, the top-level netlist for earlgrey is a combination of hand-written SystemVerilog RTL with auto-generated sections for wiring of comportability interfaces.
There is a script for this auto-generation, centered around the top-level descriptor file `top_earlgrey.hjson` found in the repository.
A full definition of this descriptor file, its features, and related scripting is forthcoming.
This tooling generates the interconnecting crossbar (via `TLUL`) as well as the instantiations at the top level.
It also feeds into this document generation to ensure that the chosen address locations are documented automatically using the data in the source files.

## Top Level vs Chip Targets

It should first be **NOTED** that there is some subtlety on the notion of hierarchy within the top level.
There is netlist automation to create the module `top_earlgrey` as indicated in sections of this specification that follow.
**On top** of that module, hierarchically in the repo, are chip level instantiation targets directed towards a particular use case.
This includes `chip_earlgrey_cw310` for use in FPGA, and `chip_earlgrey_asic` for use (eventually) in a silicon implementation.
These chip level targets will include the actual pads as needed by the target platform.
At the time of this writing the two are not in perfect synchronization, but the intention will be for them to be as identical as possible.
Where appropriate, including the block diagram below, notes will be provided where the hierarchy subtleties are explained.

## FPGA Platform

**TODO: This section needs to be updated once pin updates are complete.**

In the FPGA platform, the logic for the JTAG and the SPI device are multiplexed within `chip_earlgrey_cw310`.
This is done for ease of programming by the external host.

## References
1. [Schiavone, Pasquale Davide, et al. "Slow and steady wins the race? A comparison of
 ultra-low-power RISC-V cores for Internet-of-Things applications."
 _27th International Symposium on Power and Timing Modeling, Optimization and Simulation
 (PATMOS 2017)_](https://doi.org/10.1109/PATMOS.2017.8106976)
