# SPI Device HWIP Technical Specification
<!-- BEGIN CMDGEN util/mdbook_regression_links.py --hjson hw/ip/spi_device/data/spi_device.hjson --top earlgrey -->
| Regression | Version | [Stages](https://opentitan.org/book/doc/project_governance/development_stages.html) | Results |
|-|-|-|-|
 [`spi_device_1r1w`](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/dashboard.html) | 2.0.0 | D2S, V2S | ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/spi_device_1r1w/test.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/spi_device_1r1w/passing.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/spi_device_1r1w/functional.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/spi_device_1r1w/code.svg) |
 [`spi_device_2p`](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/dashboard.html) | 2.0.0 | D2S, V2S | ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/spi_device_2p/test.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/spi_device_2p/passing.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/spi_device_2p/functional.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/spi_device_2p/code.svg) |

This IP has been taped out in Earl Grey 1.0.0. The corresponding documentation and regression results can be found [here](https://opentitan.org/earlgrey_1.0.0/book/hw/ip/spi_device/index.html).

<!-- END CMDGEN -->

# Overview

## Features

### SPI Flash emulation and Passthrough Modes

- Supports Serial Flash emulation (Flash mode).
  - 24 Flash command information slots, with configurable address/dummy/payload size per command.
  - HW processing of Read Status, Read JEDEC ID, Read SFDP, EN4B/EX4B, WREN/WRDI, and various Read commands.
  - 16-depth command/address FIFOs and 256-byte payload buffer for command uploading for SW emulation of writes and other commands.
  - 2x 1kB read buffers for Read commands, targeting bulk read use-cases with double-buffering of data.
  - 1kB mailbox buffer with a configurable mailbox address.
- Supports SPI Passthrough to downstream Flash (Passthrough mode).
  - 256-bit filter CSR for filtering inadmissible commands by opcode.
  - Configurable translation of command address bytes and first 4 bytes of command payload.
  - Configurable interception of Read Status, read JEDEC ID, and Read SFDP commands, as well as reads to the mailbox region.
  - Per-command control of SPI PADs' output enable.
  - Optional 2-stage read pipeline to decrease timing pressure.
  - Tracking of current 3B/4B address mode.
  - Targets 33MHz in Quad Read mode, falls back to 25MHz.

### TPM over SPI

- Compliant with [TPM PC Client Platform][TPM PCCP].
- Up to 64B compile-time configurable read and write data buffer (default: 4B).
- 1 TPM command (8-bit) and 1 address (24-bit) buffer.
- HW-controlled wait state.
- Shared SPI with other SPI Device functionalities. Unique CS# for the TPM
  - Flash or Passthrough mode can be active with TPM mode, with the shared pins allowing them to time-multiplex the bus.
- HW-processed registers for read requests during FIFO mode.
  - `TPM_ACCESS_x`, `TPM_STS_x`, `TPM_INTF_CAPABILITY`, `TPM_INT_ENABLE`, `TPM_INT_STATUS`, `TPM_INT_VECTOR`, `TPM_DID_VID`, `TPM_RID`.
  - `TPM_HASH_START` returns `FFh`.
- Supports 5 Localities (compile-time parameter).

## Description

The SPI Device module consists of three functions: SPI Flash mode, SPI passthrough mode, and TPM over SPI mode.

In Flash mode, the SPI Device IP behaves as a Serial Flash device by recognizing SPI Flash commands and processing those commands in HW.
The commands processed by HW are Read Status 1-3, Read JEDEC ID, Read SFDP, EN4B/EX4B, WREN/WRDI, and read commands with aid of SW.
The IP supports Normal Read, Fast Read, Fast Read Dual Output, Fast Read Quad Output.
This version of IP does not support Dual IO, Quad IO, QPI commands.

Read commands are processed using a double-buffering scheme, with interrupts to signal when it is necessary for SW to fill a portion of the read buffer with more data.
This scheme is to support bulk read transfers (for example, Firmware image loading).
The SPI Device IP cannot be used to fully emulate a generic SPI Flash device with random-access reads/writes.

In Passthrough mode, the SPI Device IP receives SPI transfers from a host system and forwards the transfers to a downstream flash device.
SW may filter prohibited commands by configuring the 256-bit [`FILTER`](doc/registers.md#filter) CSR.
The SPI Device can cancel the ongoing transfer if the received opcode bit is set in the filter CSR by de-asserting CSb and gating SCK to the downstream flash device.

In Passthrough mode, SW may also configure CSRs to change the address and/or the first 4 bytes of payload on-the-fly.
The address translation feature allows SW to maintain A/B binary images for reads, without the aid of SW on the host system.
The payload translation may be used to change the payload of Write Status commands to not allow certain fields bits being modified.

In Passthrough mode, the SPI Device IP can be configured to process certain commands internally.
In is recommended that internally-processed commands are filtered from reaching the downstream flash.
Mailbox reads are an exception, as they share the Read command opcode.

In TPM mode, SW can receive TPM commands with a payload and respond to read commands using the TPM submodule of the SPI Device IP.
The submodule provides the command, address, write, and read FIFOs for SW to communicate with the TPM host system.
The submodule also manages a set of the FIFO registers and can return read requests in HW quickly, without SW intervention.


### SPI Device Modes and Active Submodules

The SPI Device IP has two flash-like modes, as well as a TPM mode.
Flash and Passthrough modes share many parts of the datapath.
With Flash mode, all commands target the SPI Device IP, and a special read buffer is available to stream data back to the host.
In passthrough mode, commands may target the SPI Device IP and/or a downstream SPI flash, and the read buffer is not available.

TPM mode has a separate CSb port, which allows the host to send TPM commands while Flash or Passthrough mode is enabled, but commands cannot be issued to both TPM mode and Flash/Passthrough modes at the same time as the SPI bus is shared between them.

| Mode        | Status | JEDEC | SFDP | Mailbox | Read | EN4B/EX4B | WREN/WRDI | Upload | Passthrough |
|:------------|:------:|:-----:|:----:|:-------:|:----:|:---------:|:---------:|:------:|:-----------:|
| Flash       |   Y    |   Y   |  Y   |    Y    |  Y   |     Y     |     Y     |   Y    |     N       |
| Passthrough |  Y/N   |  Y/N  | Y/N  |   Y/N   |  N   |     Y     |     Y     |   Y    |     Y       |

*Y/N*: Based on the configuration of [`INTERCEPT_EN`](doc/registers.md#intercept_en).

### Clocking Requirements

SPI Device requires the core clock to have a frequency that is at least 1/4 the SPI clock frequency.

## Compatibility

The SPI Device HWIP supports emulating an EEPROM when in SPI Flash mode.
The TPM submodule conforms to the [TPM over SPI 2.0][] specification.
The TPM operation follows [TCG PC Client Platform TPM Profile Specification Section 7][TPM PCCP].

[TPM over SPI 2.0]: https://trustedcomputinggroup.org/wp-content/uploads/Trusted-Platform-Module-Library-Family-2.0-Level-00-Revision-1.59_pub.zip
[TPM PCCP]: https://trustedcomputinggroup.org/resource/pc-client-platform-tpm-profile-ptp-specification/
