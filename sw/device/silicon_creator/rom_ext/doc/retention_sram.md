# Retention SRAM

## Overview

The retention SRAM is a small SRAM in the always-on (AON) power domain.
Its contents are kept across deep sleep and, unless the ROM is configured otherwise, across resets other than a power-on reset (PoR).
The silicon creator boot stages (ROM and `ROM_EXT`) use it to hand information to later boot stages and to the next boot.
Most importantly, it holds the message area through which silicon owner code and `ROM_EXT` exchange [boot services][boot-services] requests and responses.

The retention SRAM is driven by an instance of the same [SRAM controller][sram-ctrl] IP as the main SRAM, so it does not show up as a separate hardware block.
In the Earl Grey memory map it is the `ram` region of the retention SRAM controller instance:

| Top level                         | Instance            | RAM base address | Size  | Register block |
|-----------------------------------|---------------------|------------------|-------|----------------|
| Earl Grey (`earlgrey_1.0.0`)      | `sram_ctrl_ret_aon` | `0x4060_0000`    | 4 KiB | `0x4050_0000`  |
| Earl Grey (`master`)              | `sram_ctrl_ret`     | `0x4060_0000`    | 8 KiB | `0x4050_0000`  |

Silicon creator software accesses it through `retention_sram_get()`, which returns a pointer to the `retention_sram_t` structure defined in [`retention_sram.h`][retention-sram-h].

## Layout

The silicon creator software defines the following 4 KiB layout at the start of the retention SRAM.
Offsets are relative to the base address.

| Offset  | Size (bytes) | Field                          | Description                                                                                         |
|---------|-------------:|--------------------------------|-----------------------------------------------------------------------------------------------------|
| `0x000` |            4 | `version`                      | Layout version. ROM writes `0x3430_5252` (ASCII `RR04`) on every boot.                              |
| `0x004` |            4 | `creator.reset_reasons`        | Reset reasons read from the reset manager by ROM on this boot.                                      |
| `0x008` |          256 | `creator.boot_svc_msg`         | [Boot services message area](#boot-services-message-area), shared with silicon owner code.          |
| `0x108` |         1652 | `creator.reserved`             | Reserved for future use by the silicon creator.                                                     |
| `0x77C` |          128 | `creator.boot_log`             | [Boot log](#boot-log) describing the current boot.                                                  |
| `0x7FC` |            4 | `creator.last_shutdown_reason` | Redacted reason of the last shutdown. Reset to `kErrorOk` when ROM re-initializes the retention SRAM. |
| `0x800` |         2048 | `owner`                        | [Silicon owner area](#silicon-owner-area).                                                          |

The first 2 KiB (`version` and the `creator` area) belong to the silicon creator; the second 2 KiB belong to the silicon owner.
Within the creator area, the boot services message area is placed at the start and the boot log and shutdown reason at the end, so that either side can grow into the reserved space without moving the other fields.

`ROM_EXT` checks `version` early in boot using `retention_sram_check_version()`.
Version `RR04` is accepted, and the engineering sample version 1 (`0x72f4_eb2e`) is upgraded in place to `RR04`.
Any other value, including the never-released versions 2 and 3, makes `ROM_EXT` abort the boot with `kErrorRetRamBadVersion`.

## Initialization and resets

On every boot, before jumping to `ROM_EXT`, ROM does the following (see `rom_init()` in [`rom.c`][rom-c]):

1. It reads the reset reasons from the reset manager.
1. If the reset reasons include PoR, or any reason selected by the OTP item `CREATOR_SW_CFG_RET_RAM_RESET_MASK`, it re-initializes the retention SRAM:
   * The SRAM controller fills the whole retention SRAM with pseudo-random data.
     The contents are therefore *not* zero after re-initialization.
   * The readback feature is configured from the upper nibble of the OTP item `OWNER_SW_CFG_ROM_SRAM_READBACK_EN`.
   * `creator.last_shutdown_reason` is set to `kErrorOk`.
1. It clears the boot log and fills in its identifier, the chip version and whether the retention SRAM was re-initialized on this boot.
1. It writes `RR04` to `version` and stores the reset reasons in `creator.reset_reasons`.

Otherwise, ROM leaves the retention SRAM untouched, so the boot services message area and the owner area survive the reset.
A PoR always re-initializes the retention SRAM, regardless of the OTP configuration.

ROM detects a wakeup from deep sleep when the only reset reason is a low power exit.
`ROM_EXT` checks the stored `creator.reset_reasons` for a low power exit to tell whether it is waking up from deep sleep, for example to decide whether to run boot services.

## Boot services message area

The 256-byte area at offset `0x008` carries one boot services message at a time.
Every message starts with a 44-byte header, `boot_svc_header_t` (see [`boot_svc_header.h`][boot-svc-header-h]):

| Offset | Size (bytes) | Field        | Description                                                                                   |
|--------|-------------:|--------------|-----------------------------------------------------------------------------------------------|
| `0x00` |           32 | `digest`     | SHA-256 digest of the message, from `identifier` to the end of the message (`length` bytes in total). |
| `0x20` |            4 | `identifier` | `0x4356_5342` (ASCII `BSVC`) for all boot services messages.                                  |
| `0x24` |            4 | `type`       | Message type.                                                                                 |
| `0x28` |            4 | `length`     | Total length of the message in bytes, including the header. Must be between 44 and 256.      |

The header is followed by a type-specific payload.
The message types are defined in [`sw/device/silicon_creator/lib/boot_svc`][boot-svc-dir], together with helper functions that fill in a message and compute its digest (`boot_svc_header_finalize()`).

### Request flow

1. Silicon owner code writes a request message into the message area.
1. Silicon owner code resets the chip.
   The reset must not be one for which ROM re-initializes the retention SRAM (see [Initialization and resets](#initialization-and-resets)), otherwise the request is lost.
   The [attestation specification][attestation] refers to this as a `BOOT_SERVICE_REQUEST` reset; there is no dedicated reset reason for it.
1. On the next boot, `ROM_EXT` looks at the message area (see `boot_svc_handler()` in [`rom_ext_boot_services.c`][rom-ext-boot-services-c]).
   If `identifier` is `BSVC`, it checks that `length` is in range and that `digest` matches, and then handles the request according to `type`.
   A message with a bad header is ignored and boot continues.
1. `ROM_EXT` writes its response to the same message area.
   Silicon owner code can read the response once it runs.

`ROM_EXT` skips boot services when waking up from deep sleep, unless the current owner configuration enables boot services after a low power wakeup.
Requests can also be delivered through the [rescue protocol][rescue].

Message types are four-character codes.
The response type of each request is the same four bytes in reverse order:

| Request              | Request type  | Response type |
|----------------------|---------------|---------------|
| `EMPTY`              | `EMPT`        | `TPME`        |
| `ENTER_RESCUE`       | `ERSQ`        | `QSRE`        |
| `NEXT_BL0_SLOT`      | `NEXT`        | `TXEN`        |
| `MIN_BL0_SEC_VER`    | `MSEC`        | `CESM`        |
| `OWNERSHIP_UNLOCK`   | `UNLK`        | `KLNU`        |
| `OWNERSHIP_ACTIVATE` | `ACTV`        | `VTCA`        |

The codes are stored as little-endian 32-bit words, e.g. `EMPT` is `0x5450_4d45`.
What each request does is described in the [secure boot specification][boot-services] and, for the ownership requests, in [ROM_EXT Ownership Transfer][rom-ext-ownership].
`ROM_EXT` leaves response messages and messages of unknown type unchanged.

## Boot log

The 128-byte boot log at offset `0x77C` (`boot_log_t`, see [`boot_log.h`][boot-log-h]) records how the device booted, for example which `ROM_EXT` and BL0 slots ran.
Its fields are described in [Boot Log][boot-log].
ROM creates the boot log on every boot and records the `ROM_EXT` slot it booted and whether it re-initialized the retention SRAM.
`ROM_EXT` fills in the remaining fields and updates the `digest` after handling boot services.
The boot log can also be requested through the [rescue protocol][rescue].

## Silicon owner area

The 2 KiB at offset `0x800` are reserved for the silicon owner.
Silicon creator boot stages do not write to this area, except that it is filled with pseudo-random data when ROM re-initializes the retention SRAM.
Silicon owner code can use it to keep state across resets and deep sleep, but must not assume any particular content after a PoR.

[attestation]: ../../../../../doc/security/specs/attestation/README.md
[boot-log]: ../../doc/boot_log.md
[boot-log-h]: ../../lib/boot_log.h
[boot-services]: ../../../../../doc/security/specs/secure_boot/README.md#boot-services
[boot-svc-dir]: ../../lib/boot_svc
[boot-svc-header-h]: ../../lib/boot_svc/boot_svc_header.h
[rescue]: rescue.md
[retention-sram-h]: ../../lib/drivers/retention_sram.h
[rom-c]: ../../rom/rom.c
[rom-ext-boot-services-c]: ../rom_ext_boot_services.c
[rom-ext-ownership]: ownership.md
[sram-ctrl]: ../../../../../hw/ip/sram_ctrl/README.md
