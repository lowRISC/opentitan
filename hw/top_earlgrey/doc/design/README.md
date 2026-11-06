# OpenTitan Earl Grey Chip Specification

**NOTE**: This doc refers to Earl Grey 2, i.e., the second generation of the discrete OpenTitan chip design currently being developed on the [`master` branch](https://github.com/lowRISC/opentitan).
For information on the taped out Earl Grey design, i.e., the first production OpenTitan silicon, refer to the documentation for the [`earlgrey_1.0.0` branch](https://github.com/lowRISC/opentitan/tree/earlgrey_1.0.0) [available here](https://opentitan.org/earlgrey_1.0.0/book/hw/top_earlgrey/doc/design/index.html).
This doc describes the hardware design.
The software (ROM, ROM_EXT) is also under development and may not yet implement all features of the hardware.

This document describes the OpenTitan Earl Grey chip functionality in detail.
For an overview, refer to the [OpenTitan Earl Grey Chip Datasheet](../datasheet.md).

# Theory of Operations

The netlist `chip_earlgrey_asic` contains the features listed in the [datasheet](../datasheet.md) and is intended for ASIC synthesis, whereas the netlist `chip_earlgrey_cw340` provides an emulation environment for the `cw340` FPGA board. Finally, `chip_earlgrey_verilator` is intended for elaboration and simulation with Verilator.
The code for Ibex is developed in its own [lowRISC repo](https://github.com/lowrisc/ibex), and is [*vendored in*](../../../../doc/contributing/hw/vendor.md) to this repository.
Surrounding Ibex is a suite of *Comportable* peripherals that follow the [Comportability Guidelines](../../../../doc/contributing/hw/comportability/README.md) for lowRISC peripheral IP.
Each of these IP has its own specification.
See the table produced in the [hardware documentation page](../../../README.md) for links to those specifications.

## Design Details

This section provides some details for the processor and the peripherals.
See their representative specifications for more information.
This section also contains a brief overview of some of the features of the final product.

### Power Domains

The design is distributed across two power domains: `Main` (default, turned off during deep sleep) and `Aon` (remains powered during deep sleep). The attribution of each instantiated IP to a power domain is done through the `domain` attribute of each instance specified in `top_earlgrey.hjson`. The tooling (`topgen`) automatically creates a wrapper for each power domain and the required connections between them (see [Power Domain Wrappers vs Top Level vs Chip Targets](#power-domain-wrappers-vs-top-level-vs-chip-targets) for details).

### Clocking and Reset

Clocks and resets are supplied from the Analog Sensor Top, referred to as [ast](../../ip/ast/README.md) from this point onwards in the document.

`ast` supplies a number of clocks into `top_earlgrey`.
- sys: main jittery system clock used for higher performance blocks and security (processor, memory and crypto blocks).
- io: a fixed clock used for peripheral blocks such as timers and I/O functionality, such as SPI or I2C.
- usb: a fixed clock used specifically for usb operations.
- aon: an always on, low frequency clock used for power management and low speed timers.

These clocks are then divided down and distributed to the rest of the system.
See [clock manager](../../ip_autogen/clkmgr/README.md) for more details.

In the low-speed external clock mode and during the life cycle clock bypass, the `io` clock drops to 48 MHz, while the clock manager steps down its dividers so that `io_div2` and `io_div4` keep their nominal frequencies (see [clock manager](../../ip_autogen/clkmgr/doc/theory_of_operation.md#clock-frequency-summary)).
Peripherals on `io`, such as SPI_HOST0 and SPI_HOST1, therefore run at half their nominal frequency in these modes, and software must account for this when it configures their clock dividers.

`ast` also supplies a number of power-okay signals to `top_earlgrey`, and these are used as asynchronous root resets.
- vcaon_pok: The always on domain of the system is ready.
- vcmain_pok: The main operating domain of the system is ready.

When one of these power-okay signals drop, the corresponding domain in `top_earlgrey` is reset.
Please refer to [reset manager](../../ip_autogen/rstmgr/README.md) for more details.
Resets throughout the design are asynchronous active low as per the Comportability specification.

Once reset, the reset vector begins in ROM, whose job is to validate code in non-volatile memory (RRAM, see the [Memory](#memory) section below) before jumping to it.
Valid code is assumed to have been instantiated into NVM, if not, the ROM shuts down the device unless prompted to bootstrap.

There are multiple avenues to load valid code into NVM:
1. JTAG initiated programming.
2. ROM bootstrap

#### AST Clocking and Reset Relationship

While the ast supplies clocks and resets to the `top_earlgrey`, it also contains additional functions that interact with the design.
These include the `RNG`, `ADC`, jittery clock controls and an assortment of other sensors.
The operating clocks and resets for these interfaces are supplied by the device in order to ensure correct synchronous operations.
The clock mapping is shown below:

| AST Port         | `top_earlgrey` Clock     |
|------------------|--------------------------|
| clk_ast_adc_i    | aon                      |
| clk_ast_alert_i  | io_div4                  |
| clk_ast_es_i     | sys                      |
| clk_ast_rng_i    | sys                      |
| clk_ast_tlul_i   | io_div4                  |
| clk_ast_usb_i    | usb                      |

The reset clock domain is identical to the table above, and the power domain mapping is shown below


| AST Port         | `top_earlgrey` Power Domain |
|------------------|-----------------------------|
| rst_ast_adc_i    | always-on                   |
| rst_ast_alert_i  | main                        |
| rst_ast_es_i     | main                        |
| rst_ast_rng_i    | main                        |
| rst_ast_tlul_i   | main                        |
| rst_ast_usb_i    | main                        |

### System Reset Handling and RRAM

Since `top_earlgrey` contains RRAM, it is important to examine the memory's relationship with resets.

Unlike flash, RRAM has no separate program or erase step; what would be a program or erase operation on flash is just a write operation on RRAM.

#### Reset due to External Supply

Device resets due to supply dropping below a specific threshold are commonly known as a "brown-out".
When this occurs, the memory macro must go through appropriate sequencing, handled between ast and the memory, to ensure it is not damaged.

#### Reset while Write in Progress

Resets that happen during a write operation need special care, because an incomplete write could leave the RRAM in an undefined state.
To that end, the RRAM controller indicates to the [pwrmgr](../../ip_autogen/pwrmgr/doc/theory_of_operation.md#abort-handling) when a write is in progress, so that a reset or low power entry request can be aborted until the write completes.


### Main processor (`core_ibex`)

The main processor (`core_ibex`) is a small and efficient, 32-bit, in-order RISC-V core.
See the [core_ibex specification](https://ibex-core.readthedocs.io/en/latest/) for more details of the core.
Ibex is integrated into Earl Grey through the [`rv_core_ibex` wrapper](../../ip_autogen/rv_core_ibex/README.md), whose parameters set the configuration below.

Earl Grey configures Ibex as follows:
- Pipeline: 3 stages (instruction fetch; decode and execute; writeback).
- Base ISA: RV32I or CHERIoT, see [CHERIoT](#cheriot) below.
- M extension with a single-cycle multiplier.
- C extension, plus the Zcb and Zcmp code size reduction extensions.
- Bit manipulation: Zba, Zbb and Zbs (B), plus Zbc (implies Zbkc), Zbkb and Zbkx.
- Zicsr, Zicntr, Zihpm and Zifencei.
- Execution modes: M (machine) and U (user).
- Smepmp: enhanced physical memory protection (ePMP) with 16 regions and a granularity of 4 bytes.
- Instruction cache: 4 KiB, 2-way set associative, with ECC and scrambling.
- Debug: 4 hardware breakpoints (triggers).

`SecureIbex` is enabled, which adds the following hardware security features (see the Ibex [security features](https://ibex-core.readthedocs.io/en/latest/03_reference/security.html)):
- Dual-core lockstep.
- Integrity checks on the register file, the instruction cache and the bus interfaces.
- Hardened program counter.
- Data-independent timing, enabled through the `cpuctrlsts` CSR.
- Dummy instruction insertion, enabled through the `cpuctrlsts` CSR.

Attached to the Ibex core are a debug module (DM) and interrupt module (PLIC).

#### CHERIoT

Ibex is built with a base ISA that can switch from RV32I to [CHERIoT](https://github.com/microsoft/cheriot-sail/releases/) version 1.0.
CHERIoT is a capability-based ISA that provides hardware-enforced memory safety.
After reset, Ibex executes RV32I and uses the ePMP for memory protection.
Software can switch to CHERIoT, or lock the RV32I mode, once through the [`CHERIOT_ENA`](../../ip_autogen/rv_core_ibex/doc/registers.md#cheriot_ena) and [`CHERIOT_LOCK`](../../ip_autogen/rv_core_ibex/doc/registers.md#cheriot_lock) registers of `rv_core_ibex`.
The selected mode stays locked until the next reset.
See [execution mode switch](../../ip_autogen/rv_core_ibex/doc/theory_of_operation.md#execution-mode-switch) for details.

A CHERIoT capability consists of a 32-bit address, 32 bits of metadata and a validity tag bit.
The [CHERIoT memory subsystem](../../../ip/cheriot_mem_sys/README.md) (`cheriot_mem_sys`) sits between the data port of Ibex and the main crossbar.
It stores the validity tags and the revocation bitmap in the [CHERIoT meta SRAM](#srams), which is separate from the memories that hold the capabilities.
It splits each data access into an access to the memory and an access to the tag.
A non-capability store clears the tag of the location it writes.

The memory subsystem also contains a background revocation engine.
The engine sweeps a range of capabilities in the Main SRAM, the Secondary SRAM or the RRAM.
It clears the tag of every capability whose base is marked as revoked in the revocation bitmap.
It raises an interrupt when a sweep completes and counts completed sweeps in an epoch register, which the CHERIoT RTOS revoker uses.

In RV32I mode, the CHERIoT meta SRAM is not accessible by software.

#### JTAG / Debug module

One feature available for Earl Grey processor core is debug access.
By interfacing with JTAG pins, logic in the debug module allows the core to enter debug mode (per RISC-V 0.13 debug spec), and gives the design the ability to inject code either into the device - by emulating an instruction - or into memory.
Full details can be found in the [rv_dm specification](../../../ip/rv_dm/README.md).

#### Interrupt Controller

Adjacent to the Ibex core is an interrupt controller that implements the RISC-V PLIC standard.
This accepts a vector of interrupt sources within the device, and assigns leveling and priority to them before sending to the core for handling.
See the details in the [rv_plic specification](../../ip_autogen/rv_plic/README.md).

#### Performance

The following numbers were measured on the first generation of Earl Grey, whose non-volatile memory was embedded flash.
They have not yet been re-measured on Earl Grey 2.

Ibex achieved a [CoreMark](https://www.eembc.org/coremark/) per MHz of 1.93 on Earl Grey.
For a detailed analysis of where this number comes from, please refer to this [GitHub issue](https://github.com/lowRISC/opentitan/issues/17370#issuecomment-1453324348).
In short, by [moving read-only data from non-volatile memory into SRAM](https://github.com/lowRISC/opentitan/issues/17370#issuecomment-1446719338) and by playing with optimization flags, a CoreMark/MHz of 2.15 is achievable.
This number is close to the maximum achievable number for Ibex with an ideal single-cycle access memory system when using the LLVM compiler.

When switching to GCC and combining the Ibex configuration used in OpenTitan Earl Grey with an idealistic single-cycle access non-volatile memory, a CoreMark/MHz number of 3.07 is achievable.
To achieve this performance, CoreMark can be compiled with GCC 9.2.0 and with the following flags: `-march=rv32imc -mabi=ilp32 -mcmodel=medany -mtune=sifive-3-series -O3 -falign-functions=16 -funroll-all-loops -finline-functions -falign-jumps=4 -mstrict-align` .

The Ibex documentation has more details on the current pipeline operation, including stall behaviour for each instruction in the [Pipeline Details](https://ibex-core.readthedocs.io/en/latest/03_reference/pipeline_details.html) section.

### Memory

The table below lists the memories of Earl Grey.
The [memory map](../memory_map.md) gives their base addresses.

| Memory            | Size    | Controller                                          | Power domain | Intended use                                  |
|-------------------|---------|-----------------------------------------------------|--------------|-----------------------------------------------|
| ROM               | 192 KiB | [`rom_ctrl`](../../../ip/rom_ctrl/README.md)        | `Main`       | Boot code                                     |
| RRAM              | 2 MiB   | [`rram_ctrl`](../../../ip/rram_ctrl/README.md)      | `Main`       | Non-volatile code and data storage            |
| OTP               | 2 KiB   | [`otp_ctrl`](../../ip_autogen/otp_ctrl/README.md)   | `Main`       | One-time programmable data                    |
| Main SRAM         | 128 KiB | [`sram_ctrl_main`](../../../ip/sram_ctrl/README.md) | `Main`       | General-purpose data (e.g., heap, stack)      |
| Secondary SRAM    | 64 KiB  | [`sram_ctrl_sec`](../../../ip/sram_ctrl/README.md)  | `Main`       | General-purpose data (e.g., heap, stack)      |
| Retention SRAM    | 8 KiB   | [`sram_ctrl_ret`](../../../ip/sram_ctrl/README.md)  | `Aon`        | Data that must be retained during deep sleep  |
| CHERIoT meta SRAM | 38 KiB  | [`sram_ctrl_meta`](../../../ip/sram_ctrl/README.md) | `Main`       | CHERIoT capability tags and revocation bitmap |

[OTBN](../../../ip/otbn/README.md) additionally contains 16 KiB of instruction memory and 32 KiB of data memory.
Software accesses them through the OTBN register interface.

#### ROM

The ROM contains the instructions that Ibex executes after it is released from reset.
Their purpose is to do a minimal subset of platform checking before checking the next stage of code.
The next stage, ROM_EXT, is stored in non-volatile memory.
It is the first piece of code that is not hard-coded into the silicon of the device, and thus must be signature checked.
The ROM verifies the signature of ROM_EXT before it jumps to it, as described in [Secure boot](#secure-boot).

#### RRAM

Earl Grey contains 2 MiB of embedded RRAM (resistive RAM), its non-volatile memory (NVM) technology: it houses ROM_EXT and subsequent software layers.

RRAM is the primary technology for code and data storage on Earl Grey.
Being a non-volatile memory technology, software must interact with the [RRAM controller](#rram-controller) to write to it rather than writing to the standard memory address space directly; unlike flash, RRAM only requires a read/write interface, with no separate erase step.
The FPGA emulation of the memory approximates the read and write speeds and non-volatile nature that the RRAM macro exhibits in silicon.

The top 3 KiB of the RRAM data partition are reserved as the OTP region and are not accessible by software (see [OTP](#otp)).

The intent is for the contents of the NVM code to survive FPGA reset as it would as a NVM in silicon.
Loading of the FPGA with initial content, or updating with new content, is described in other software specifications.
The SPI device peripheral is provided as a method to bulk-load the NVM.
The processor debug port (via JTAG) is also available for code loading.
See those specifications for more details.

#### OTP

Earl Grey has no OTP macro.
Instead, the [OTP controller](../../ip_autogen/otp_ctrl/README.md) stores its 2 KiB of one-time programmable memory (1032 words of 16 bit) in the OTP region of the RRAM.
The RRAM controller implements OTP semantics on that region: bits can only be set, never cleared.

#### SRAMs

The Main SRAM (128 KiB) and the Secondary SRAM (64 KiB) are available for data storage (stack, heap, etc.) by the Ibex processor.
They occupy one contiguous address range of 192 KiB.
They are also available for code storage, though that is not their intended purpose.
Depending on an OTP setting, execution from them is controlled either by a lockable firmware register or by the life cycle state.
In CHERIoT mode, both can store capabilities that can be revoked at a granularity of 8 bytes.

The Retention SRAM (8 KiB) is in the `Aon` power domain and retains its contents during deep sleep.
Code execution from the Retention SRAM is not supported.

The CHERIoT meta SRAM (38 KiB) stores the data of the [CHERIoT memory subsystem](#cheriot):
- the revocation bitmap for the Main and Secondary SRAMs (3 KiB),
- the capability tags for the RRAM (32 KiB), and
- the capability tags for the Main and Secondary SRAMs (3 KiB).

Only `cheriot_mem_sys` accesses the CHERIoT meta SRAM directly.
Software can access only the revocation bitmap, through a window of `cheriot_mem_sys`, and only in CHERIoT mode.
When software triggers the hardware initialization of the CHERIoT meta SRAM, its SRAM controller fills it with zeros instead of pseudo-random data, so that all tags and revocation bits start cleared.
Code execution from it is not supported.

All four SRAMs have 7 ECC bits per 32-bit word and are scrambled by their [SRAM controller](../../../ip/sram_ctrl/README.md) with a reduced-round PRINCE cipher.
For the CHERIoT meta SRAM, address scrambling is currently disabled.

### Secure boot

Earl Grey follows the [Secure Boot](../../../../doc/security/specs/secure_boot/README.md) specification.
The ROM verifies the signature of ROM_EXT before it executes ROM_EXT.
Earl Grey supports post-quantum secure boot with ML-DSA-87 signatures, whose verification [OTBN](#otbn) accelerates.

The ROM reads the Silicon Creator public keys from the `ROT_CREATOR_AUTH_CODESIGN` partition of [OTP](#otp), which has the following key slots:
- 4 ECDSA-P256 key slots, and
- 4 ML-DSA-87 key slots.

Every ROM_EXT must have a valid ECDSA-P256 signature.
An ML-DSA-87 signature is required in addition unless ML-DSA-87 verification is disabled in OTP.
In the `TEST_UNLOCKED*` life cycle states, the ROM does not check ML-DSA-87 signatures.

Each key slot has a key type, which determines the life cycle states in which the ROM accepts the key:

| Key type | `TEST_UNLOCKED*` | `DEV` | `PROD`, `PROD_END` | `RMA` |
|----------|------------------|-------|--------------------|-------|
| test     | yes              | no    | no                 | yes   |
| dev      | yes              | yes   | no                 | yes   |
| prod     | yes              | yes   | yes                | yes   |

The `ROT_CREATOR_AUTH_STATE` partition of OTP holds the state of each key slot: blank, provisioned or revoked.
The ROM accepts only provisioned keys.

### Peripherals

Earl Grey contains a suite of "peripherals", or subservient execution units connected to the Ibex processor by means of a bus interconnect.
Each of these peripherals follows an interface scheme dictated in the [Comportability Specification.](../../../../doc/contributing/hw/comportability/README.md).
That specification details how the processor communicates with the peripheral (via TLUL interconnect); how the peripheral communicates with the chip IO (via fixed or multiplexable IO); how the peripheral communicates with the processor (interrupts); and how the peripheral communicates security events (via alerts).
See that specification for generic details on this scheme.

#### Chip IO Peripherals

##### Pin Multiplexor Module (`pinmux`)

The pin multiplexor's purpose is to route between peripherals and the available multiplexable IO of the chip.
At this time, the pin multiplexor is provided, but it is not used to its full potential.
In addition, the multiplexor device manages control or pad attributes like drive strength, technology (OD, OS, etc), pull up, pull down, etc., of the chip's external IO.
It is notable that there are many differences between an FPGA implementation of Earl Grey and an ASIC version when it comes to pins and pads.
Some pad attributes with analog characteristics like drive strength, slew rate and Open Drain technology are not supported on all platforms.

The pin multiplexor is a peripheral on the TLUL bus, with collections of registers that provide software configurability.
See the [pinmux specification](../../ip_autogen/pinmux/README.md) for how to connect peripheral IO to chip IO and for information on pad control features.

##### UART

The chip contains four UART peripherals (`uart0` to `uart3`), each of which implements single-lane duplex UART functionality.
The outputs and inputs can be configured to any chip IO via the [pinmux](../../ip_autogen/pinmux/README.md).

See the [UART specification](../../../ip/uart/README.md) for more details on this peripheral.

##### GPIO

The chip contains two GPIO peripherals (`gpio0` and `gpio1`) that each create 32 bits of bidirectional communication with the outside world via the pinmux.
Via pinmux any of the 32 pins of either GPIO can be connected to any of the 47 MIO chip pins, in any direction.
See the [GPIO specification](../../ip_autogen/gpio/README.md) for more details on this peripheral.
See the [pinmux specification](../../ip_autogen/pinmux/README.md) for how to connect peripheral IO to chip IO.

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

##### USB device

The chip contains a single module that supports USB device mode at full speed.
In addition to normal functionality, USB suspend / resume is supported alongside the chip's low power modes.

See the [USB device specification](../../../ip/usbdev/README.md) for more details.

##### I2C

The chip contains three I2C peripherals (`i2c0` to `i2c2`).
Each one can operate as an I2C controller or as an I2C target.
They support Standard-mode (100 kbaud), Fast-mode (400 kbaud) and Fast-mode Plus (1 Mbaud).
In controller mode, they support clock stretching and multi-controller operation with clock synchronization and bus arbitration.
In target mode, they stretch the clock automatically and support programmable automatic ACK control.

The SCL and SDA signals of each I2C peripheral can be connected to any of the multiplexable IO (MIO) of the chip via the [pinmux](../../ip_autogen/pinmux/README.md).
The I2C peripherals drive SCL and SDA as a virtual open drain: they only pull the lines low and otherwise release them.
A bus pulled up above the pad supply voltage needs a **BidirOd** pad with open drain enabled (see [Open drain / virtual open drain](#open-drain--virtual-open-drain)).
Each I2C peripheral has its own reset, which software can assert through the [reset manager](../../ip_autogen/rstmgr/README.md).

See the [I2C specification](../../../ip/i2c/README.md) for more details.

##### I3C

The chip contains two I3C peripherals (`i3c0` and `i3c1`).
Each one can operate as an I3C Primary Controller or as an I3C Target.

Both peripherals have the same configuration:

| Parameter or feature           | Value                                                   |
|--------------------------------|---------------------------------------------------------|
| IP clock (`clk_i`, `ClkFreq`)  | `io` clock, 96 MHz                                      |
| Half-cycle SCL high extension  | Enabled (`HalfCycleScl` = 1)                            |
| Virtual Targets (`NumTargets`) | 2                                                       |
| Message buffer                 | 4 KiB                                                   |
| Device Address Table           | 32 entries                                              |
| Device Characteristics Table   | 32 entries                                              |
| Other clocks                   | `clk_aon_i`: `aon` clock; `scan_clk_i`: `io_div2` clock |

Each I3C peripheral has its own reset, which software can assert through the [reset manager](../../ip_autogen/rstmgr/README.md).

At 96 MHz, the Controller forms each SCL period from 8 IP clock cycles, i.e. 83.3 ns, so SCL runs at up to 12 MHz.
The maximum data rates of long transfers are therefore 10.6 Mbps in SDR mode and 19.2 Mbps in HDR-DDR mode.
On a Mixed Fast Bus, these rates require the `io` clock to be within +/-11% of 96 MHz (see the [I3C integration notes](../../../ip/i3c/doc/integration_notes.md#half-cycle-scl-high-extension)).
For Targets with a large `tSCO` delay, the data rate may need to be lower (see the [I3C integration notes](../../../ip/i3c/doc/integration_notes.md#ip-clock-frequency)).

The SCL, SDA and SDA pull-up (`ctrl_sda_pu`) signals of each I3C peripheral can be connected to the multiplexable IO (MIO) of the chip via the [pinmux](../../ip_autogen/pinmux/README.md).
The chip uses the Virtual Open Drain output driver style of the I3C peripheral (`rtl/io_vod/i3c_io_pkg.sv`), in which the peripheral emulates open drain signaling on SDA.
Software shall therefore leave the open drain and virtual open drain attributes of the I3C pads disabled in the pinmux (`MIO_PAD_ATTR.OD_EN` and `MIO_PAD_ATTR.VIRTUAL_OD_EN`).
The board shall connect an external pull-up resistor between the `ctrl_sda_pu` pin and SDA; the peripheral drives this pin high while the SDA pull-up is required.
The Active Controller always drives SCL in push-pull mode, so SCL needs no pull-up.
The high-keeper enables and the SCL pull-up enable of the peripherals are not connected, so the board shall provide passive high-keepers where the bus requires them.

Each I3C peripheral has a Target Reset Detector in the secondary partition of the IP (`i3c_part_secondary`, see the [I3C integration notes](../../../ip/i3c/doc/integration_notes.md#target-reset-detector)).
The detector of `i3c0` is in the `Aon` power domain, and the detector of `i3c1` is in the `Main` power domain.
Both wake-up requests are connected to the [power manager](../../ip_autogen/pwrmgr/README.md), but only the one from `i3c0` can wake the chip from deep sleep.
The detectors observe SCL and SDA through their own pinmux inputs, so software shall select the same pads for them as for the SCL and SDA inputs of their I3C peripheral ([#31841](https://github.com/lowRISC/opentitan/issues/31841)).
The request of the detectors to reset their I3C peripheral is not connected yet ([#31839](https://github.com/lowRISC/opentitan/issues/31839)), and they do not expose a request to reset the whole chip.

See the [I3C specification](../../../ip/i3c/README.md) for more details, and its [implementation status](../../../ip/i3c/doc/implementation_status.md) for the capabilities that the RTL does not implement yet.

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

##### KMAC

KMAC implements the [SHA-3](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf) hash functions (SHA3-224, SHA3-256, SHA3-384 and SHA3-512), the extendable-output functions SHAKE and cSHAKE (128 and 256), and the [KMAC](https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-185.pdf) message authentication code.
KMAC keys can be up to 512b long.
On Earl Grey, the Keccak core is first-order masked to protect against side-channel analysis.

Software uses KMAC through registers and a message FIFO.
KMAC also has an application interface through which other hardware blocks use it without software involvement: the key manager DPE, the life cycle controller, the ROM controller and OTBN.
The key manager DPE can sideload a key into KMAC, which software cannot read.

See the [KMAC specification](../../../ip/kmac/README.md) for more details.

##### OTBN

The OpenTitan Big Number Accelerator (OTBN) is a coprocessor for asymmetric cryptography, including post-quantum cryptography (PQC), elliptic curve cryptography and RSA.
Its PQC support includes hardened ML-DSA and ML-KEM.
It has a 32b control path and a 256b data path with full-width and 32b SIMD instructions.
OTBN has its own 16 KiB instruction memory and 32 KiB data memory, of which software can access 16 KiB over the bus.
Both memories are scrambled with keys from the OTP controller.

OTBN obtains random numbers from both EDN instances (see [Entropy Distribution Network](#entropy-distribution-network)).
It can use KMAC for hashing and contains a masking accelerator interface for first-order masked operations.
The key manager DPE can sideload a key into OTBN.

See the [OTBN specification](../../../ip/otbn/README.md) for more details.

##### Key Manager DPE

The key manager DPE derives keys for identity, attestation and sealing without exposing the underlying secrets to software.
It implements the [DICE Protection Environment (DPE)](https://trustedcomputinggroup.org/wp-content/uploads/TCG-DICE-Protection-Environment-Specification_14february2023-1.pdf).
On Earl Grey, it has 4 key slots, each of which holds one DICE context.
Software can derive a child slot from any valid slot; per-slot policies constrain derivation.

The key manager DPE uses KMAC as its key derivation function.
Its inputs include the creator root key from the OTP controller, the creator and owner seeds from the RRAM controller, the ROM digest from the ROM controller, and a diversification value from the life cycle controller.
It can generate keys for software or sideload them into AES, HMAC, KMAC and OTBN.

See the [key manager DPE specification](../../../ip/keymgr_dpe/README.md) for more details.

##### Life Cycle Controller

The life cycle controller manages the [device life cycle](../../../../doc/security/specs/device_life_cycle/README.md) state, which is redundantly encoded and stored in OTP.
It decodes the state and broadcasts redundantly encoded enable signals to other blocks, for example to enable the CPU, debug or DFT features.
Life cycle transitions are requested through registers or through JTAG.
Important transitions are guarded by tokens, which the life cycle controller hashes with KMAC.
On a transition to RMA, the life cycle controller requests the RRAM controller to wipe the RRAM.
The alert handler can escalate to the life cycle controller.
The life cycle controller then moves into a virtual scrap state, which is not programmed into OTP and lasts until the next reset, and asserts an escalation signal to all blocks with an escalation action.

See the [life cycle controller specification](../../../ip/lc_ctrl/README.md) for more details.

##### OTP Controller

The OTP controller provides one-time programmable storage that is logically divided into partitions.
Partitions can be locked, integrity checked with digests, and scrambled.
The OTP controller checks the partitions periodically in the background.
It provides keys and seeds to other blocks over dedicated hardware interfaces, including the scrambling keys of the SRAMs, the instruction cache, OTBN and the RRAM, the creator root key of the key manager DPE, and the life cycle state.

Earl Grey has no OTP macro.
The OTP controller stores its data in the OTP region of the RRAM through the RRAM controller (see [OTP](#otp)).

See the [OTP controller specification](../../ip_autogen/otp_ctrl/README.md) for more details.

##### ROM Controller

The ROM controller connects the ROM to the system bus.
The ROM contents are stored scrambled, and the ROM controller descrambles them on reads.
After reset and before the CPU starts, the ROM controller reads the entire ROM and computes its digest with KMAC.
It compares the digest with the expected digest stored in the top words of the ROM and reports the result to the power manager, which stops chip startup on a mismatch.
The power manager ignores the result when both DFT and hardware debug are enabled, i.e., in the `TEST_UNLOCKED*` and `RMA` life cycle states.
The ROM controller also passes the digest to the key manager DPE.

See the [ROM controller specification](../../../ip/rom_ctrl/README.md) for more details.

##### SRAM Controller

Earl Grey contains four SRAM controller instances: one each for the Main SRAM, the Secondary SRAM, the Retention SRAM and the CHERIoT meta SRAM (see [SRAMs](#srams)).
Each SRAM controller scrambles the addresses and data of its SRAM with a reduced-round PRINCE cipher.
It requests ephemeral scrambling keys from the OTP controller, and software can request a new key at any time.
It can initialize the SRAM with pseudo-random data in hardware.
It also controls whether code can execute from the SRAM, checks bus integrity, and can check each read and write with a readback to detect faults.

See the [SRAM controller specification](../../../ip/sram_ctrl/README.md) for more details.

##### Sensor Control

The sensor control block is the comportable front-end of the [analog sensor top](../../ip/ast/README.md) (`ast`).
It receives alerts from the `ast` sensors and forwards them to the alert handler.
It can wake the device from sleep on these alerts, and it provides status readback of the `ast`.
Sensor control is in the `Aon` power domain.

See the [sensor control specification](../../ip/sensor_ctrl/README.md) for more details.

#### Other peripherals

##### Timer(s)

Timers are critical for operating systems to ensure guaranteed performance for users.
To some level they are even required by the RISC-V specification.
Earl Grey contains two timer peripherals.

The [timer](../../../ip/rv_timer/README.md) (`rv_timer`) provides one 64b free-running timer for the Ibex processor, with a programmable prescaler and step.
It raises an interrupt when it reaches a compare value.

The [AON timer](../../../ip/aon_timer/README.md) (`aon_timer`) is in the `Aon` power domain and runs on the always-on clock.
It contains two timers:
- A 64b wakeup timer, which can wake the device from sleep and raise an interrupt.
- A 32b watchdog timer, which backstops the processor in case it becomes unresponsive.
  Software must periodically reset ("pet") the watchdog counter.
  When the counter reaches the bark threshold, the watchdog raises an interrupt, a non-maskable interrupt (NMI) to Ibex, and a wakeup request.
  When the counter reaches the bite threshold, the watchdog requests a system reset from the power manager.
  Software can lock the watchdog configuration, and can configure the watchdog to pause during sleep.

Both AON timers pause while the life cycle controller signals escalation.

##### RRAM Controller

The RRAM controller manages an emulated RRAM (resistive RAM) macro, and is Earl Grey's primary non-volatile storage peripheral for code and data, having replaced the flash controller in that role. It also houses emulated OTP (one-time programmable) functionality, replacing the use of a dedicated OTP macro.

The primary read path for this data is in the standard memory address space.
Writes on the other hand, need to be initiated by software  which must interact with the RRAM controller.

Unlike flash, RRAM does not require a separate erase step before writing: the RRAM controller exposes only read and write commands, and software can write new data to a word directly without first erasing its page.
Read, as mentioned above, is standard, and uses the chip memory address space.

Writes are significantly slower than reads, and must be aligned to an RRAM word (128b) and sized as a multiple of it.
The RRAM controller peripheral in this release approximates the expected timing of the silicon RRAM macro.

Security is also a concern, since secret data can be stored in the RRAM.
The RRAM controller provides per-page memory protection, on-the-fly XEX scrambling (using the PRINCE cipher) with a key sideloaded from OTP, end-to-end bus integrity, and per-word address infection to protect against a range of physical and software attacks.
A secure wipe of the RRAM contents with random data is also performed on entry to the RMA lifecycle state.
For more details see the [RRAM controller module specification](../../../ip/rram_ctrl/README.md).

### Interconnection

Interconnecting the processor and peripheral and memory units is a bus network built upon the TileLink-Uncached-Light protocol.
See the [OpenTitan bus specification](../../../ip/tlul/README.md) for more details.

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

The base addresses of the memory and peripherals are defined in this [table](../memory_map.md).

The choice of memory, or lack thereof at location 0x0 confers two exclusive benefits:
- If there are no memories at location 0x0, then null pointers will immediately error and be noticed by software (the xbar will fail to decode and route)
- If SRAM is placed at 0, accesses to data located within 2KB of 0x0 can be accomplished with a single instruction and thus reduce code size.

For the purpose of `top_earlgrey`, the first option has been chosen to benefit software development and testing.

## Entropy Distribution Network

`top_earlgrey` has two [EDN](../../../ip/edn/README.md) instances, which are connected to one [CSRNG](../../../ip/csrng/README.md) instance (which in turn is connected to one [Entropy Source](../../../ip/entropy_src/README.md) instance).
The first EDN instance, `u_edn0`, has eight endpoints, which are connected to: Key Manager DPE, OTP Controller, Analog Sensor Top, KMAC Accelerator, Alert Handler, AES Accelerator, the `URND` port of OTBN, and the Ibex RISC-V Core.
The second EDN instance, `u_edn1`, has a single endpoint, which is connected to the `RND` port of OTBN.
The second EDN instance, `u_edn1` is intended to be configured to deliver highest-quality entropy, e.g., for the generation of cryptographic secrets.
The first EDN instance, `u_edn0` is intended to be configured to deliver entropy at a higher rate and thus slightly lower quality.


## Hardware Interfaces

### Pinout

<!-- BEGIN CMDGEN util/design/gen-top-docs.py -t hw/top_earlgrey/data/autogen/top_earlgrey.gen.hjson -g pinout -->
| ID   | Name          | Bank   | Type         | Connection Type   | Description                                |
|:-----|:--------------|:-------|:-------------|:------------------|:-------------------------------------------|
| 0    | POR_N         | VCC    | InputStd     | manual            | System reset based on VCC                  |
| 1    | PORA_N        | VIOA   | InputStd     | manual            | System reset based on VIOA                 |
| 2    | USB_P         | VCC    | DualBidirTol | manual            | USB P signal                               |
| 3    | USB_N         | VCC    | DualBidirTol | manual            | USB N signal                               |
| 4    | CC1           | AVCC   | BidirTol     | manual            | ADC input 1                                |
| 5    | CC2           | AVCC   | BidirTol     | manual            | ADC input 2                                |
| 6    | RRAM_ANALOG   | VCC    | AnalogIn0    | manual            | RRAM analog test signal                    |
| 7    | SPI_HOST_D0   | VIOA   | BidirStd     | direct            | SPI host data                              |
| 8    | SPI_HOST_D1   | VIOA   | BidirStd     | direct            | SPI host data                              |
| 9    | SPI_HOST_D2   | VIOA   | BidirStd     | direct            | SPI host data                              |
| 10   | SPI_HOST_D3   | VIOA   | BidirStd     | direct            | SPI host data                              |
| 11   | SPI_HOST_CLK  | VIOA   | BidirStd     | direct            | SPI host clock                             |
| 12   | SPI_HOST_CS_L | VIOA   | BidirStd     | direct            | SPI host chip select                       |
| 13   | SPI_DEV_D0    | VIOA   | BidirStd     | direct            | SPI device data                            |
| 14   | SPI_DEV_D1    | VIOA   | BidirStd     | direct            | SPI device data                            |
| 15   | SPI_DEV_D2    | VIOA   | BidirStd     | direct            | SPI device data                            |
| 16   | SPI_DEV_D3    | VIOA   | BidirStd     | direct            | SPI device data                            |
| 17   | SPI_DEV_CLK   | VIOA   | InputStd     | direct            | SPI device clock                           |
| 18   | SPI_DEV_CS_L  | VIOA   | InputStd     | direct            | SPI device chip select                     |
| 0    | IOA0          | VIOA   | BidirStd     | muxed             | Muxed IO pad                               |
| 1    | IOA1          | VIOA   | BidirStd     | muxed             | Muxed IO pad                               |
| 2    | IOA2          | VIOA   | BidirStd     | muxed             | Muxed IO pad                               |
| 3    | IOA3          | VIOA   | BidirStd     | muxed             | Muxed IO pad                               |
| 4    | IOA4          | VIOA   | BidirStd     | muxed             | Muxed IO pad                               |
| 5    | IOA5          | VIOA   | BidirStd     | muxed             | Muxed IO pad                               |
| 6    | IOA6          | VIOA   | BidirOd      | muxed             | Muxed IO pad                               |
| 7    | IOA7          | VIOA   | BidirOd      | muxed             | Muxed IO pad                               |
| 8    | IOA8          | VIOA   | BidirOd      | muxed             | Muxed IO pad                               |
| 9    | IOB0          | VIOB   | BidirStd     | muxed             | Muxed IO pad                               |
| 10   | IOB1          | VIOB   | BidirStd     | muxed             | Muxed IO pad                               |
| 11   | IOB2          | VIOB   | BidirStd     | muxed             | Muxed IO pad                               |
| 12   | IOB3          | VIOB   | BidirStd     | muxed             | Muxed IO pad                               |
| 13   | IOB4          | VIOB   | BidirStd     | muxed             | Muxed IO pad                               |
| 14   | IOB5          | VIOB   | BidirStd     | muxed             | Muxed IO pad                               |
| 15   | IOB6          | VIOB   | BidirStd     | muxed             | Muxed IO pad                               |
| 16   | IOB7          | VIOB   | BidirStd     | muxed             | Muxed IO pad                               |
| 17   | IOB8          | VIOB   | BidirStd     | muxed             | Muxed IO pad                               |
| 18   | IOB9          | VIOB   | BidirOd      | muxed             | Muxed IO pad                               |
| 19   | IOB10         | VIOB   | BidirOd      | muxed             | Muxed IO pad                               |
| 20   | IOB11         | VIOB   | BidirOd      | muxed             | Muxed IO pad                               |
| 21   | IOB12         | VIOB   | BidirOd      | muxed             | Muxed IO pad                               |
| 22   | IOC0          | VCC    | BidirStd     | muxed             | Muxed IO pad                               |
| 23   | IOC1          | VCC    | BidirStd     | muxed             | Muxed IO pad                               |
| 24   | IOC2          | VCC    | BidirStd     | muxed             | Muxed IO pad                               |
| 25   | IOC3          | VCC    | BidirStd     | muxed             | Muxed IO pad                               |
| 26   | IOC4          | VCC    | BidirStd     | muxed             | Muxed IO pad                               |
| 27   | IOC5          | VCC    | BidirStd     | muxed             | Muxed IO pad                               |
| 28   | IOC6          | VCC    | BidirStd     | muxed             | Muxed IO pad                               |
| 29   | IOC7          | VCC    | BidirStd     | muxed             | Muxed IO pad                               |
| 30   | IOC8          | VCC    | BidirStd     | muxed             | Muxed IO pad                               |
| 31   | IOC9          | VCC    | BidirStd     | muxed             | Muxed IO pad                               |
| 32   | IOC10         | VCC    | BidirOd      | muxed             | Muxed IO pad                               |
| 33   | IOC11         | VCC    | BidirOd      | muxed             | Muxed IO pad                               |
| 34   | IOC12         | VCC    | BidirOd      | muxed             | Muxed IO pad                               |
| 35   | IOR0          | VCC    | BidirStd     | muxed             | Muxed IO pad                               |
| 36   | IOR1          | VCC    | BidirStd     | muxed             | Muxed IO pad                               |
| 37   | IOR2          | VCC    | BidirStd     | muxed             | Muxed IO pad                               |
| 38   | IOR3          | VCC    | BidirStd     | muxed             | Muxed IO pad                               |
| 39   | IOR4          | VCC    | BidirStd     | muxed             | Muxed IO pad                               |
| 40   | IOR5          | VCC    | BidirStd     | muxed             | Muxed IO pad                               |
| 41   | IOR6          | VCC    | BidirStd     | muxed             | Muxed IO pad                               |
| 42   | IOR7          | VCC    | BidirStd     | muxed             | Muxed IO pad                               |
| 19   | IOR8          | VCC    | BidirOd      | direct            | Dedicated sysrst_ctrl output (ec_rst_l)    |
| 20   | IOR9          | VCC    | BidirOd      | direct            | Dedicated sysrst_ctrl output (flash_wp_l)) |
| 43   | IOR10         | VCC    | BidirOd      | muxed             | Muxed IO pad                               |
| 44   | IOR11         | VCC    | BidirOd      | muxed             | Muxed IO pad                               |
| 45   | IOR12         | VCC    | BidirOd      | muxed             | Muxed IO pad                               |
| 46   | IOR13         | VCC    | BidirOd      | muxed             | Muxed IO pad                               |

<!-- END CMDGEN -->

#### Open drain / virtual open drain

Pads of type **BidirOd** and **BidirStd** support **open drain** and **virtual open drain**, respectively.
When open drain or virtual open drain is enabled in pinmux's attributes for such a pad, the PMOS transistor that would otherwise drive the output high for a logic 1 is disabled.
Thus for a logic 1, the impedance of the pad is essentially the output impedance of the CMOS transistor pair (which is specified in the data sheet of the chip).

However, there still exists a parallel connection to the supply rail through a protection circuit.
Therefore:
- For **BidirOd** pads in open drain mode, the output protection circuit allows voltages that exceed the supply voltage.
  The maximum voltage that may be applied in this case is derived from the maximum voltage of the specific pad type (which is specified in the data sheet of the chip).
- For **BidirStd** pads, the maximum voltage that may be applied is the supply voltage (within tolerance, as specified in the data sheet of the chip).

All other pad types support neither open drain nor virtual open drain.


# RTL Implementation Notes

At this time, the top-level netlist for earlgrey is a combination of hand-written SystemVerilog RTL with auto-generated sections for wiring of comportability interfaces.
There is a script for this auto-generation, centered around the top-level descriptor file `top_earlgrey.hjson` found in the repository.
A full definition of this descriptor file, its features, and related scripting is forthcoming.
This tooling generates the interconnecting crossbar (via `TLUL`) as well as the instantiations at the top level.
It also feeds into this document generation to ensure that the chosen address locations are documented automatically using the data in the source files.

## Power Domain Wrappers vs Top Level vs Chip Targets

It should first be **NOTED** that there is some subtlety on the notion of hierarchy within the top level.
There is automation to create the power domain wrapper modules `earlgrey_pd_main` and `earlgrey_pd_aon` as indicated in sections of this specification that follow. On top of those, there is the `top_earlgrey` wrapper which instantiates both wrappers, establishes the inter-power-domain connections, and exposes all signals that are required further up the hierarchy at its port.

**On top** of `top_earlgrey`, highest up in the design hierarchy, are chip level instantiation targets directed towards a particular use case.
This includes `chip_earlgrey_cw340` for use in FPGA, `chip_earlgrey_asic` for use in silicon implementations, and finally `chip_earlgrey_verilator`.

These chip level targets will include the actual pads as needed by the target platform, and further target-specific circuitry (such as e.g., clock generators for the FPGA targets or a hard macro for the USB differential receiver on the ASIC target).
Due to these target-specific requirements, the chip levels may substantially differ from each other.
Where appropriate, including the block diagram below, notes will be provided where the hierarchy subtleties are explained.

## FPGA Platform

The FPGA platform is the `chip_earlgrey_cw340` target for the ChipWhisperer CW340 board.
Its pin assignment is listed in the [CW340 pinout table](../../ip_autogen/pinmux/doc/pinout_cw340.md).
The SPI device uses dedicated pads, as on the ASIC target.

`chip_earlgrey_cw340` contains an FPGA-only memory backdoor loader (`bkdr_loader`, enabled by the `BkdrLoaderEn` parameter).
It sits between the JTAG and reset pads and `top_earlgrey`.
It becomes active after reset if both TAP strap pins are high.
While active, it keeps `top_earlgrey` in reset and lets the external host preload the non-volatile and volatile memories over JTAG.
Once deactivated, it forwards the JTAG signals to `top_earlgrey` and releases the reset.
This loader does not exist on the ASIC target.
