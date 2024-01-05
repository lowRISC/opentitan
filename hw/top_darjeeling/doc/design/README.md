# OpenTitan Darjeeling Chip Specification

This document describes the OpenTitan Darjeeling chip functionality in detail.
For an overview, refer to the [OpenTitan Darjeeling Chip Datasheet](../datasheet.md).

# Theory of Operations

The netlist `chip_darjeeling_asic` contains the features listed above and is intended for ASIC synthesis, whereas the netlist `chip_darjeeling_cw310` provides an emulation environment for the `cw310` FPGA board.
The code for Ibex is developed in its own [lowRISC repo](https://github.com/lowrisc/ibex), and is [*vendored in*](../../../../doc/contributing/hw/vendor.md) to this repository.
Surrounding Ibex is a suite of *Comportable* peripherals that follow the [Comportability Guidelines](../../../../doc/contributing/hw/comportability/README.md) for lowRISC peripheral IP.
Each of these IP has its own specification.
See the table produced in the [hardware documentation page](../../../README.md) for links to those specifications.

## Design Details

This section provides some details for the processor and the peripherals.
See their representative specifications for more information.
This section also contains a brief overview of some of the features of the final product.

### Clocking and Reset

Clocks and resets are supplied from the Analog Sensor Top, referred to as [ast](../../ip/ast/README.md)) from this point onwards in the document.

`ast` supplies a number of clocks into `top_darjeeling`.
- sys: main jittery system clock used for higher performance blocks and security (processory, memory and crypto blocks).
- io: a fixed clock used for peripheral blocks such as timers and I/O functionality, such as SPI or I2C.
- aon: an always on, low frequency clock used for power management and low speed timers.

These clocks are then divided down and distributed to the rest of the system.
See [clock manager](../../../ip/clkmgr/README.md)) for more details.

`ast` also supplies a number of power-okay signals to `top_darjeeling`, and these are used as asynchronous root resets.
- vcaon_pok: The always on domain of the system is ready.
- vcmain_pok: The main operating domain of the system is ready.

When one of these power-okay signals drop, the corresponding domain in `top_darjeeling` is reset.
Please refer to [reset manager](../../../ip/rstmgr/README.md)) for more details.
Resets throughout the design are asynchronous active low as per the Comportability specification.

Once reset, the reset vector begins in ROM, whose job is to validate code in the embedded flash before jumping to it.
Valid code is assumed to have been instantiated into the flash, if not, the ROM shuts down the device unless prompted to bootstrap.

There are multiple avenues to load valid code into the flash:
1. JTAG initiated flash programming.
2. ROM bootstrap

#### AST Clocking and Reset Relationship

While the ast supplies clocks and resets to the `top_darjeeling`, it also contains additional functions that interact with the design.
These include the `RNG`, `ADC`, jittery clock controls and an assortment of other sensors.
The operating clocks and resets for these interfaces are supplied by the device in order to ensure correct synchronous operations.
The clock mapping is shown below:

| AST Port         | `top_darjeeling` Clock     |
|------------------|----------------------------|
| clk_ast_adc_i    | aon                        |
| clk_ast_alert_i  | io_div4                    |
| clk_ast_es_i     | sys                        |
| clk_ast_rng_i    | sys                        |
| clk_ast_tlul_i   | io_div4                    |

The reset clock domain is identical to the table above, and the power domain mapping is shown below


| AST Port         | `top_darjeeling` Power Domain |
|------------------|-------------------------------|
| rst_ast_adc_i    | always-on                     |
| rst_ast_alert_i  | main                          |
| rst_ast_es_i     | main                          |
| rst_ast_rng_i    | main                          |
| rst_ast_tlul_i   | main                          |

### System Reset Handling and Flash

Since `top_darjeeling` contains flash, it is important to examine the memory's relationship with resets.

For flash, resets that occur during a stateful operation (program or erase) must be carefully handled to ensure the flash memory is not damaged.
There are three reset scenarios:

* Reset due to external supply lowering.
* Reset due to internal peripheral request.
* Reset due to lower power entry and exit.

#### Reset due to External Supply

Device resets due to supply dropping below a specific threshold are commonly known as "brown-out".
When this occurs, the flash memory must go through specialized sequencing to ensure the cells are not damaged.
This process is handled exclusively between ast and the flash.
Please see the [relevant section](../../ip/ast/README.md#main-vcc-power-detection-and-flash-protection) for more details.

#### Reset due to Internal Request

When the device receives an internal request to reset (for example [aon_timer](../../../ip/aon_timer/README.md#aon-watchdog-timer)), device power is kept on and the flash is directly reset.
It is assumed that the flash device, when powered, will be able to correctly handle such a sequence and properly protect itself.

#### Reset due to Low Power Entry

When the device receives a low power entry request while flash activity is ongoing, the [pwrmgr](../../../ip/pwrmgr/README.md#abort-handling)) is responsible for ensuring the entry request is aborted.


### Main processor (`core_ibex`)

The main processor (`core_ibex`) is a small and efficient, 32-bit, in-order RISC-V core with a 2-stage pipeline that implements the RV32IMC instruction set architecture.
It was initially developed as part of the [PULP platform](https://www.pulp-platform.org) under the name "Zero-riscy" [\[1\]](https://doi.org/10.1109/PATMOS.2017.8106976), and has been contributed to [lowRISC](https://www.lowrisc.org) who maintains it and develops it further.
See the [core_ibex specification](https://ibex-core.readthedocs.io/en/latest/) for more details of the core.
In addition to the standard RISC-V functionality, Ibex implements M (machine) and U (user) mode per the RISC-V standard.
Attached to the Ibex core are a debug module (DM) and interrupt module (PLIC).

#### JTAG / Debug module

One feature available for Darjeeling processor core is debug access.
By interfacing with JTAG pins, logic in the debug module allows the core to enter debug mode (per RISC-V 0.13 debug spec), and gives the design the ability to inject code either into the device - by emulating an instruction - or into memory.
Full details can be found in the [rv_dm specification](../../../ip/rv_dm/README.md).

#### Interrupt Controller

Adjacent to the Ibex core is an interrupt controller that implements the RISC-V PLIC standard.
This accepts a vector of interrupt sources within the device, and assigns leveling and priority to them before sending to the core for handling.
See the details in the [rv_plic specification](../../ip_autogen/rv_plic/README.md).

#### Performance

Ibex currently achieves a [CoreMark](https://www.eembc.org/coremark/) per MHz of 2.36 on the darjeeling verilator system.
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

Darjeeling contains 1024kB of embedded-flash (e-flash) memory for code storage.
This is intended to house the boot loader mentioned above, as well as the operating system and application that layers on top.
At this time there is no operating system provided; applications are simple proof of concept code to show that the chip can do with a bare-metal framework.

Embedded-flash is the intended technology for a silicon design implementing the full OpenTitan device.
It has interesting and challenging parameters that are unique to the technology that the silicon is implemented in.
Darjeeling, as an FPGA proof of concept, will model these parameters in its emulation of the memory in order to prepare for the replacement with the silicon flash macros that will come.
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

### Secure boot

Darjeeling follows the [Secure Boot](../../../../doc/security/specs/secure_boot/README.md) specification. The `ROM` has 3 key slots
which are allocated as follows:

| Slot | Role | Name |
|------|------|------|
| 0 | test | `test 0` |
| 1 | test | `test 1` |
| 2 | dev | `dev 0` |
| 3 | dev | `dev 1` |
| 4 | prod | `prod 0` |
| 5 | prod | `prod 1` |
| 6 | prod | `prod 2` |

### Peripherals

Darjeeling contains a suite of "peripherals", or subservient execution units connected to the Ibex processor by means of a bus interconnect.
Each of these peripherals follows an interface scheme dictated in the [Comportability Specification.](../../../../doc/contributing/hw/comportability/README.md).
That specification details how the processor communicates with the peripheral (via TLUL interconnect); how the peripheral communicates with the chip IO (via fixed or multiplexable IO); how the peripheral communicates with the processor (interrupts); and how the peripheral communicates security events (via alerts).
See that specification for generic details on this scheme.

#### Chip IO Peripherals

##### Pin Multiplexor Module (`pinmux`)

The pin multiplexor's purpose is to route between peripherals and the available multiplexable IO of the chip.
At this time, the pin multiplexor is provided, but it is not used to its full potential.
In addition, the multiplexor device manages control or pad attributes like drive strength, technology (OD, OS, etc), pull up, pull down, etc., of the chip's external IO.
It is notable that there are many differences between an FPGA implementation of Darjeeling and an ASIC version when it comes to pins and pads.
Some pad attributes with analog characteristics like drive strength, slew rate and Open Drain technology are not supported on all platforms.

The pin multiplexor is a peripheral on the TLUL bus, with collections of registers that provide software configurability.
See the [pinmux specification](../../../ip/pinmux/README.md) for how to connect peripheral IO to chip IO and for information on pad control features.

##### UART

The chip contains one UART peripheral that implement single-lane duplex UART functionality.
The outputs and inputs can be configured to any chip IO via the [pinmux](../../../ip/pinmux/README.md).

See the [UART specification](../../../ip/uart/README.md) for more details on this peripheral.

##### GPIO

The chip contains one GPIO peripheral that creates 32 bits of bidirectional communication with the outside world via the pinmux.
Via pinmux any of the 32 pins of GPIO can be connected to any of the 32 MIO chip pins, in any direction.
See the [GPIO specification](../../../ip/gpio/README.md) for more details on this peripheral.
See the [pinmux specification](../../../ip/pinmux/README.md) for how to connect peripheral IO to chip IO.

##### SPI device


The SPI device implements multiple modes:
- Firmware mode
- TPM mode
- Flash mode
- Passthrough mode

Firmware Mode is a generic data transfer mode.
It can be used by software to construct a simple firmware upgrade mechanism for in-field devices.

TPM mode supports SPI transfers in compliance with the TPM PC Client Platform.
The interface is single data lane and supports built-in data back pressuring.

Flash mode supports serial flash emulation.
Typical commands such as read status, address mode, read data and program data are either natively supported or can be emulated.

Passthrough mode supports serial flash passthrough from an upstream SPI host to a downstream serial flash device.

See the [SPI device specification](../../../ip/spi_device/README.md) for more details.

##### I2C host

In order to be able to command I2C devices on systems where Darjeeling will be included, I2C host functionality will be required.
This will include standard, full, and fast mode, up to 1Mbaud.
More details of the I2C host module will come in a later specification update.
The pins of the I2C host will be available to connect to any of the multiplexable IO (MIO) of the Darjeeling device.
More than one I2C host module might be instantiated in the top level.

#### Security Peripherals

##### AES

[AES](https://nvlpubs.nist.gov/nistpubs/fips/nist.fips.197.pdf) is the primary [symmetric encryption](https://en.wikipedia.org/wiki/Symmetric-key_algorithm) and decryption mechanism used in OpenTitan protocols.
AES runs with key sizes of 128b, 192b, or 256b.
The module can select encryption or decryption of data that arrives in 16 byte quantities to be encrypted or decrypted using different block cipher modes of operation.
It supports [ECB mode](https://en.wikipedia.org/wiki/Block_cipher_mode_of_operation#ECB), [CBC mode](https://en.wikipedia.org/wiki/Block_cipher_mode_of_operation#CBC), [CFB mode](https://en.wikipedia.org/wiki/Block_cipher_mode_of_operation#CFB), [OFB mode](https://en.wikipedia.org/wiki/Block_cipher_mode_of_operation#OFB) and [CTR mode](https://en.wikipedia.org/wiki/Block_cipher_mode_of_operation#CTR).

The [GCM mode](https://en.wikipedia.org/wiki/Block_cipher_mode_of_operation#GCM) is not implemented in hardware, but can be constructed using AES in counter mode.
The integrity tag calculation can be implemented in Ibex and accelerated via bitmanip instructions.

Details on how to write key and data material into the peripheral, how to initiate encryption and decryption, and how to read out results, are available in the [AES specification](../../../ip/aes/README.md).

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

Details on how to write key and data material into the peripheral, how to initiate hashing / authentication, and how to read out results, are available in the [SHA/HMAC specification](../../../ip/hmac/README.md).

##### Alert Handler

Alerts, as defined in the [Comportability Specification](../../../../doc/contributing/hw/comportability/README.md), are defined as security-sensitive interrupts that need to be handled in a timely manner to respond to a security threat.
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

The specification for the timer can be found [here](../../../ip/rv_timer/README.md).

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
For more details see the [flash controller module specification](../../../ip/flash_ctrl/README.md).

### Interconnection

Interconnecting the processor and peripheral and memory units is a bus network built upon the TileLink-Uncached-Light protocol.
See the [OpenTitan bus specification](../../../ip/tlul/README.md) for more details.

#### Topology
`top_darjeeling` has a two-level hierarchy for its bus network.
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

For the purpose of `top_darjeeling`, the first option has been chosen to benefit software development and testing

<!-- BEGIN CMDGEN util/design/gen-top-docs.py -t hw/top_darjeeling/data/autogen/top_darjeeling.gen.hjson -g mmap -->
| Name              | Type          | Byte Address      |
|:------------------|:--------------|:------------------|
| uart0             | uart          | 0x30010000 (regs) |
| gpio              | gpio          | 0x30000000 (regs) |
| spi_device        | spi_device    | 0x30310000 (regs) |
| i2c0              | i2c           | 0x30080000 (regs) |
| rv_timer          | rv_timer      | 0x30100000 (regs) |
| otp_ctrl          | otp_ctrl      | 0x30130000 (core) |
|                   |               | 0x30138000 (prim) |
| lc_ctrl           | lc_ctrl       | 0x30140000 (regs) |
| alert_handler     | alert_handler | 0x30150000 (regs) |
| spi_host0         | spi_host      | 0x30300000 (regs) |
| pwrmgr_aon        | pwrmgr        | 0x30400000 (regs) |
| rstmgr_aon        | rstmgr        | 0x30410000 (regs) |
| clkmgr_aon        | clkmgr        | 0x30420000 (regs) |
| pinmux_aon        | pinmux        | 0x30460000 (regs) |
| aon_timer_aon     | aon_timer     | 0x30470000 (regs) |
| ast               | ast           | 0x30480000 (regs) |
| sensor_ctrl       | sensor_ctrl   | 0x30020000 (regs) |
| soc_proxy         | soc_proxy     | 0x22030000 (core) |
|                   |               | 0x40000000 (ctn)  |
| sram_ctrl_ret_aon | sram_ctrl     | 0x30500000 (regs) |
|                   |               | 0x30600000 (ram)  |
| rv_dm             | rv_dm         | 0x00040000 (mem)  |
|                   |               | 0x21200000 (regs) |
| rv_plic           | rv_plic       | 0x28000000 (regs) |
| aes               | aes           | 0x21100000 (regs) |
| hmac              | hmac          | 0x21110000 (regs) |
| kmac              | kmac          | 0x21120000 (regs) |
| otbn              | otbn          | 0x21130000 (regs) |
| keymgr_dpe        | keymgr_dpe    | 0x21140000 (regs) |
| csrng             | csrng         | 0x21150000 (regs) |
| edn0              | edn           | 0x21170000 (regs) |
| edn1              | edn           | 0x21180000 (regs) |
| sram_ctrl_main    | sram_ctrl     | 0x211c0000 (regs) |
|                   |               | 0x10000000 (ram)  |
| sram_ctrl_mbox    | sram_ctrl     | 0x211d0000 (regs) |
|                   |               | 0x11000000 (ram)  |
| rom_ctrl0         | rom_ctrl      | 0x00008000 (rom)  |
|                   |               | 0x211e0000 (regs) |
| rom_ctrl1         | rom_ctrl      | 0x00020000 (rom)  |
|                   |               | 0x211e1000 (regs) |
| dma               | dma           | 0x22010000 (regs) |
| mbx0              | mbx           | 0x22000000 (core) |
| mbx1              | mbx           | 0x22000100 (core) |
| mbx2              | mbx           | 0x22000200 (core) |
| mbx3              | mbx           | 0x22000300 (core) |
| mbx4              | mbx           | 0x22000400 (core) |
| mbx5              | mbx           | 0x22000500 (core) |
| mbx6              | mbx           | 0x22000600 (core) |
| mbx_jtag          | mbx           | 0x22000800 (core) |
| mbx_pcie0         | mbx           | 0x22040000 (core) |
| mbx_pcie1         | mbx           | 0x22040100 (core) |
| rv_core_ibex      | rv_core_ibex  | 0x211f0000 (cfg)  |

<!-- END CMDGEN -->


## Entropy Distribution Network

`top_darjeeling` has two [EDN](../../../ip/edn/README.md) instances, which are connected to one [CSRNG](../../../ip/csrng/README.md) instance (which in turn is connected to an external entropy source vendor hardware IP block).
The first EDN instance, `u_edn0`, has eight endpoints, which are connected to: Key Manager, OTP Controller, Analog Sensor Top, KMAC Accelerator, Alert Handler, AES Accelerator, the `URND` port of OTBN, and the Ibex RISC-V Core.
The second EDN instance, `u_edn1`, has one endpoint that is connected to the `RND` port of OTBN and seven endpoints that are tied off.
The second EDN instance, `u_edn1` is intended to be configured to deliver highest-quality entropy, e.g., for the generation of cryptographic secrets.
The first EDN instance, `u_edn0` is intended to be configured to deliver entropy at a higher rate and thus slightly lower quality.


## Hardware Interfaces

### Pinout

<!-- BEGIN CMDGEN util/design/gen-top-docs.py -t hw/top_darjeeling/data/autogen/top_darjeeling.gen.hjson -g pinout -->
| ID   | Name             | Bank   | Type      | Connection Type   | Description                |
|:-----|:-----------------|:-------|:----------|:------------------|:---------------------------|
| 0    | POR_N            | VIO    | InputStd  | manual            | System reset               |
| 1    | JTAG_TCK         | VIO    | InputStd  | manual            | JTAG TCK signal            |
| 2    | JTAG_TMS         | VIO    | InputStd  | manual            | JTAG TMS signal            |
| 3    | JTAG_TDI         | VIO    | InputStd  | manual            | JTAG TDI signal            |
| 4    | JTAG_TDO         | VIO    | BidirStd  | manual            | JTAG TDO signal            |
| 5    | JTAG_TRST_N      | VIO    | InputStd  | manual            | JTAG TRST_N signal         |
| 6    | OTP_EXT_VOLT     | VIO    | AnalogIn1 | manual            | OTP external voltage input |
| 7    | SPI_HOST_D0      | VIO    | BidirStd  | direct            | SPI host data              |
| 8    | SPI_HOST_D1      | VIO    | BidirStd  | direct            | SPI host data              |
| 9    | SPI_HOST_D2      | VIO    | BidirStd  | direct            | SPI host data              |
| 10   | SPI_HOST_D3      | VIO    | BidirStd  | direct            | SPI host data              |
| 11   | SPI_HOST_CLK     | VIO    | BidirStd  | direct            | SPI host clock             |
| 12   | SPI_HOST_CS_L    | VIO    | BidirStd  | direct            | SPI host chip select       |
| 13   | SPI_DEV_D0       | VIO    | BidirStd  | direct            | SPI device data            |
| 14   | SPI_DEV_D1       | VIO    | BidirStd  | direct            | SPI device data            |
| 15   | SPI_DEV_D2       | VIO    | BidirStd  | direct            | SPI device data            |
| 16   | SPI_DEV_D3       | VIO    | BidirStd  | direct            | SPI device data            |
| 17   | SPI_DEV_CLK      | VIO    | InputStd  | direct            | SPI device clock           |
| 18   | SPI_DEV_CS_L     | VIO    | InputStd  | direct            | SPI device chip select     |
| 19   | SPI_DEV_TPM_CS_L | VIO    | InputStd  | direct            | SPI device TPM chip select |
| 20   | UART_RX          | VIO    | InputStd  | direct            | UART receive               |
| 21   | UART_TX          | VIO    | BidirStd  | direct            | UART transmit              |
| 22   | I2C_SCL          | VIO    | BidirStd  | direct            | I2C clock                  |
| 23   | I2C_SDA          | VIO    | BidirStd  | direct            | I2C data                   |
| 24   | GPIO0            | VIO    | BidirStd  | direct            | GPIO pad                   |
| 25   | GPIO1            | VIO    | BidirStd  | direct            | GPIO pad                   |
| 26   | GPIO2            | VIO    | BidirStd  | direct            | GPIO pad                   |
| 27   | GPIO3            | VIO    | BidirStd  | direct            | GPIO pad                   |
| 28   | GPIO4            | VIO    | BidirStd  | direct            | GPIO pad                   |
| 29   | GPIO5            | VIO    | BidirStd  | direct            | GPIO pad                   |
| 30   | GPIO6            | VIO    | BidirStd  | direct            | GPIO pad                   |
| 31   | GPIO7            | VIO    | BidirStd  | direct            | GPIO pad                   |
| 32   | GPIO8            | VIO    | BidirStd  | direct            | GPIO pad                   |
| 33   | GPIO9            | VIO    | BidirStd  | direct            | GPIO pad                   |
| 34   | GPIO10           | VIO    | BidirStd  | direct            | GPIO pad                   |
| 35   | GPIO11           | VIO    | BidirStd  | direct            | GPIO pad                   |
| 36   | GPIO12           | VIO    | BidirStd  | direct            | GPIO pad                   |
| 37   | GPIO13           | VIO    | BidirStd  | direct            | GPIO pad                   |
| 38   | GPIO14           | VIO    | BidirStd  | direct            | GPIO pad                   |
| 39   | GPIO15           | VIO    | BidirStd  | direct            | GPIO pad                   |
| 40   | GPIO16           | VIO    | BidirStd  | direct            | GPIO pad                   |
| 41   | GPIO17           | VIO    | BidirStd  | direct            | GPIO pad                   |
| 42   | GPIO18           | VIO    | BidirStd  | direct            | GPIO pad                   |
| 43   | GPIO19           | VIO    | BidirStd  | direct            | GPIO pad                   |
| 44   | GPIO20           | VIO    | BidirStd  | direct            | GPIO pad                   |
| 45   | GPIO21           | VIO    | BidirStd  | direct            | GPIO pad                   |
| 46   | GPIO22           | VIO    | BidirStd  | direct            | GPIO pad                   |
| 47   | GPIO23           | VIO    | BidirStd  | direct            | GPIO pad                   |
| 48   | GPIO24           | VIO    | BidirStd  | direct            | GPIO pad                   |
| 49   | GPIO25           | VIO    | BidirStd  | direct            | GPIO pad                   |
| 50   | GPIO26           | VIO    | BidirStd  | direct            | GPIO pad                   |
| 51   | GPIO27           | VIO    | BidirStd  | direct            | GPIO pad                   |
| 52   | GPIO28           | VIO    | BidirStd  | direct            | GPIO pad                   |
| 53   | GPIO29           | VIO    | BidirStd  | direct            | GPIO pad                   |
| 54   | GPIO30           | VIO    | BidirStd  | direct            | GPIO pad                   |
| 55   | GPIO31           | VIO    | BidirStd  | direct            | GPIO pad                   |
| 56   | SOC_GPI0         | VIO    | InputStd  | direct            | SoC general purpose input  |
| 57   | SOC_GPI1         | VIO    | InputStd  | direct            | SoC general purpose input  |
| 58   | SOC_GPI2         | VIO    | InputStd  | direct            | SoC general purpose input  |
| 59   | SOC_GPI3         | VIO    | InputStd  | direct            | SoC general purpose input  |
| 60   | SOC_GPI4         | VIO    | InputStd  | direct            | SoC general purpose input  |
| 61   | SOC_GPI5         | VIO    | InputStd  | direct            | SoC general purpose input  |
| 62   | SOC_GPI6         | VIO    | InputStd  | direct            | SoC general purpose input  |
| 63   | SOC_GPI7         | VIO    | InputStd  | direct            | SoC general purpose input  |
| 64   | SOC_GPI8         | VIO    | InputStd  | direct            | SoC general purpose input  |
| 65   | SOC_GPI9         | VIO    | InputStd  | direct            | SoC general purpose input  |
| 66   | SOC_GPI10        | VIO    | InputStd  | direct            | SoC general purpose input  |
| 67   | SOC_GPI11        | VIO    | InputStd  | direct            | SoC general purpose input  |
| 68   | SOC_GPO0         | VIO    | BidirStd  | direct            | SoC general purpose output |
| 69   | SOC_GPO1         | VIO    | BidirStd  | direct            | SoC general purpose output |
| 70   | SOC_GPO2         | VIO    | BidirStd  | direct            | SoC general purpose output |
| 71   | SOC_GPO3         | VIO    | BidirStd  | direct            | SoC general purpose output |
| 72   | SOC_GPO4         | VIO    | BidirStd  | direct            | SoC general purpose output |
| 73   | SOC_GPO5         | VIO    | BidirStd  | direct            | SoC general purpose output |
| 74   | SOC_GPO6         | VIO    | BidirStd  | direct            | SoC general purpose output |
| 75   | SOC_GPO7         | VIO    | BidirStd  | direct            | SoC general purpose output |
| 76   | SOC_GPO8         | VIO    | BidirStd  | direct            | SoC general purpose output |
| 77   | SOC_GPO9         | VIO    | BidirStd  | direct            | SoC general purpose output |
| 78   | SOC_GPO10        | VIO    | BidirStd  | direct            | SoC general purpose output |
| 79   | SOC_GPO11        | VIO    | BidirStd  | direct            | SoC general purpose output |
| 0    | MIO0             | VIO    | BidirStd  | muxed             | Muxed IO pad               |
| 1    | MIO1             | VIO    | BidirStd  | muxed             | Muxed IO pad               |
| 2    | MIO2             | VIO    | BidirStd  | muxed             | Muxed IO pad               |
| 3    | MIO3             | VIO    | BidirStd  | muxed             | Muxed IO pad               |
| 4    | MIO4             | VIO    | BidirStd  | muxed             | Muxed IO pad               |
| 5    | MIO5             | VIO    | BidirStd  | muxed             | Muxed IO pad               |
| 6    | MIO6             | VIO    | BidirStd  | muxed             | Muxed IO pad               |
| 7    | MIO7             | VIO    | BidirStd  | muxed             | Muxed IO pad               |
| 8    | MIO8             | VIO    | BidirStd  | muxed             | Muxed IO pad               |
| 9    | MIO9             | VIO    | BidirStd  | muxed             | Muxed IO pad               |
| 10   | MIO10            | VIO    | BidirStd  | muxed             | Muxed IO pad               |
| 11   | MIO11            | VIO    | BidirStd  | muxed             | Muxed IO pad               |

<!-- END CMDGEN -->

# RTL Implementation Notes

At this time, the top-level netlist for darjeeling is a combination of hand-written SystemVerilog RTL with auto-generated sections for wiring of comportability interfaces.
There is a script for this auto-generation, centered around the top-level descriptor file `top_darjeeling.hjson` found in the repository.
A full definition of this descriptor file, its features, and related scripting is forthcoming.
This tooling generates the interconnecting crossbar (via `TLUL`) as well as the instantiations at the top level.
It also feeds into this document generation to ensure that the chosen address locations are documented automatically using the data in the source files.

## Top Level vs Chip Targets

It should first be **NOTED** that there is some subtlety on the notion of hierarchy within the top level.
There is netlist automation to create the module `top_darjeeling` as indicated in sections of this specification that follow.
**On top** of that module, hierarchically in the repo, are chip level instantiation targets directed towards a particular use case.
This includes `chip_darjeeling_cw310` for use in FPGA, and `chip_darjeeling_asic` for use (eventually) in a silicon implementation.
These chip level targets will include the actual pads as needed by the target platform.
At the time of this writing the two are not in perfect synchronization, but the intention will be for them to be as identical as possible.
Where appropriate, including the block diagram below, notes will be provided where the hierarchy subtleties are explained.

## FPGA Platform

**TODO: This section needs to be updated once pin updates are complete.**

In the FPGA platform, the logic for the JTAG and the SPI device are multiplexed within `chip_darjeeling_cw310`.
This is done for ease of programming by the external host.

## References
1. [Schiavone, Pasquale Davide, et al. "Slow and steady wins the race? A comparison of
 ultra-low-power RISC-V cores for Internet-of-Things applications."
 _27th International Symposium on Power and Timing Modeling, Optimization and Simulation
 (PATMOS 2017)_](https://doi.org/10.1109/PATMOS.2017.8106976)
