# SPI Device HWIP Technical Specification

[`spi_device`](https://reports.opentitan.org/hw/ip/spi_device/dv/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/spi_device/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/spi_device/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/spi_device/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/spi_device/code.svg)

# Overview

## Features

### SPI Flash/ Passthrough Modes

- Support Serial Flash emulation
  - HW processed Read Status, Read JEDEC ID, Read SFDP, EN4B/ EX4B, and multiple read commands
  - 16 depth Command/ Address FIFOs and 256B Payload buffer for command upload
  - 2x 1kB read buffer for read commands
  - 1kB mailbox buffer and configurable mailbox target address
- Support SPI passthrough
  - Filtering of inadmissible commands (256-bit filter CSR)
  - Address translation for read commands
  - First 4B payload translation
  - HW control of SPI PADs' output enable based on command information list
  - SW configurable internal command process for Read Status, Read JEDEC ID, Read SFDP, and read access to the mailbox space
  - Targets 33MHz @ Quad read mode, fall backs to 25MHz
  - Optional pipelined reads to decrease timing pressure for passthrough mode
- Automated tracking of 3B/ 4B address mode in the flash and passthrough modes
- 24 entries of command information slots
  - Configurable address/ dummy/ payload size per opcode

### TPM over SPI

- In compliance with [TPM PC Client Platform][TPM PCCP]
- up to 64B compile-time configurable read and write data buffer (default: 4B)
- 1 TPM command (8b) and 1 address (24bit) buffer
- HW controlled wait state
- Shared SPI with other SPI Device functionalities. Unique CS# for the TPM
  - Flash or Passthrough mode can be active with TPM mode, with the shared pins allowing them to time-multiplex the bus.
- HW processed registers for read requests during FIFO mode
  - TPM_ACCESS_x, TPM_STS_x, TPM_INTF_CAPABILITY, TPM_INT_ENABLE, TPM_INT_STATUS, TPM_INT_VECTOR, TPM_DID_VID, TPM_RID
  - TPM_HASH_START returns FFh
- 5 Locality (compile-time parameter)

## Description

The SPI device module consists of three functions, SPI Flash mode, SPI passthrough mode, and TPM over SPI mode.

The SW can receive TPM commands with payload (address and data) and respond to the read commands with the return data using the TPM submodule in the SPI_DEVICE HWIP.
The submodule provides the command, address, write, and read FIFOs for the SW to communicate with the TPM host system.
The submodule also supports the SW by managing a certain set of the FIFO registers and returning the read request by HW quickly.

In Flash mode, SPI Device HWIP behaves as a Serial Flash device by recognizing SPI Flash commands and processing those commands by HW.
The commands processed by HW are Read Status (1, 2, 3), Read JEDEC ID, Read SFDP, EN4B/ EX4B, and read commands with aid of SW.
The IP supports Normal Read, Fast Read, Fast Read Dual Output, Fast Read Quad Output.
This version of IP does not support Dual IO, Quad IO, QPI commands.

In Passthrough mode, SPI Device receives SPI transactions from a host system and forwards the transactions to a downstream flash device.
SW may filter prohibited commands by configuring 256-bit [`FILTER`](doc/registers.md#filter) CSR.
The IP cancels ongoing transaction if the received opcode matches to the filter CSR by de-asserting CSb and gating SCK to the downstream flash device.

SW may program CSRs to change the address and/or the first 4 bytes of payload on-the-fly in Passthrough mode.
The address translation feature allows SW to maintain A/B binary images without aids of the host system.
The payload translation may be used to change the payload of Write Status commands to not allow certain fields to be modified.

In Passthrough mode, parts of the Flash modules can be active.
While in Passthrough mode, SW may configure the IP to process certain commands internally.
SW is recommended to filter the commands being processed internally.
Mailbox is an exception as it shares the Read command opcode.

### SPI Device Modes and Active Submodules

SPI Device HWIP has two flash-like modes + TPM mode.
Flash and Passthrough modes share many parts of the datapath.
With Flash mode, all commands target the internal node, and a special read buffer is available to stream data back to the host in FIFO style.
With Passthrough mode, commands may target the internal node and/or a downstream SPI flash, and the read buffer is not available.
TPM mode only shares the SPI and has separate CSb port, which allows that the host sends TPM commands while other SPI mode is active.

Mode     | Status | JEDEC | SFDP | Mailbox | Read | Addr4B | Upload | Passthrough
---------|--------|-------|------|---------|------|--------|--------|-------------
Flash    |  Y     |   Y   |   Y  |   Y     |   Y  |   Y    |   Y    |
Passthru |  Y/N   |  Y/N  |  Y/N |  Y/N    |   N  |   Y    |   Y    |     Y

*Y/N*: Based on INTERCEPT_EN

### Clocking Requirements

SPI Device requires the core clock to have a frequency that is at least 1/4 the SPI clock frequency.

## Compatibility

The SPI device supports emulating an EEPROM (SPI flash mode in this document).
The TPM submodule conforms to the [TPM over SPI 2.0][] specification. The TPM operation follows [TCG PC Client Platform TPM Profile Specification Section 7][TPM PCCP].

[TPM over SPI 2.0]: https://trustedcomputinggroup.org/wp-content/uploads/Trusted-Platform-Module-Library-Family-2.0-Level-00-Revision-1.59_pub.zip
[TPM PCCP]: https://trustedcomputinggroup.org/resource/pc-client-platform-tpm-profile-ptp-specification/
