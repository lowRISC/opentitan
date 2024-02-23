# ROM_EXT Rescue Protocol

## Introduction

The ROM_EXT rescue protocol permits the chip owner to perform device diagnostic and management actions when there is no functional application firmware.

These actions include:
- Flashing a new application image.
- Interacting with Boot Services.
- Requesting the Boot Log data.
- Performing Ownership Transfer.

Currently, the rescue protocol uses the console UART as the main communication channel.
In the future, rescue operations may be available via additional interfaces.

## Basic Operation

In order to interact with the rescue protocol, the user needs to signal to the ROM_EXT that rescue a rescue operation is desired.

Once signalled, the ROM_EXT will acknowledge entry into rescue mode and the user can then specify a specific rescue action and either upload or download any data block associated with that action.

Rescue mode is exited via either an in-band or out-of-band reset signal.

## Serial Rescue Protocol

### Requesting Rescue

In order to signal to the ROM_EXT that a rescue operation is desired, the user should assert the serial break condition for at least 350us while the ROM_EXT boots.
When the ROM_EXT detects the serial break condition, it will respond with an acknowledgement:

```
rescue: remember to clear break
```

Upon entry into rescue mode, the user should clear the serial break condition to allow further interaction with rescue mode.

### Rescue Operations

By default, rescue will enter firmware rescue mode and will prompt the user to upload a new firmware image via the Xmodem-CRC protocol.
Alternate modes are requested by sending the mode's 4-byte code followed by a newline character.

> NOTE: All of the mode codes avoid using capical `C` (ASCII `0x43`) because that character is part of Xmodem-CRC's signaling.

The following sections detail each of the supported alternate modes.

#### Firmware Rescue (`RESQ`)

The firmware rescue mode may be requested with the 4-byte code `RESQ`.
The ROM_EXT will acknowledge entry of this mode with the following message:

```
mode: RESQ
ok: send firmware via xmodem-crc
```

The ROM_EXT will then prompt for the transfer to start by sending the Xmodem-CRC start character (which is the ASCII character `C`).

#### Request Boot Log Data (`BLOG`)

The user may request a copy of the Boot Log with the 4-byte code `BLOG`.
The ROM_EXT will acknowledge this request with the following message:

```
mode: BLOG
ok: receive boot_log via xmodem-crc
```

The ROM_EXT will then transmit the boot log data structure to the user via the Xmodem-CRC protocol.
After completing this action, the ROM_EXT will switch back to firmware rescue mode.

#### Send a Boot Services Request (`BREQ`)

The user may request to send a Boot Services request to the ROM_EXT with the 4-byte code `BREQ`.
The ROM_EXT will acknowledge this request with the following message:

```
mode: BREQ
ok: send boot_svc request via xmodem-crc
```

The ROM_EXT will then will prompt for the transfer to start by sending the Xmodem-CRC start character (which is the ASCII character `C`).
After completing this action, the ROM_EXT will switch back to firmware rescue mode.


#### Request the last Boot Services Response (`BRSP`)

The user may request the last boot services response with the 4-byte code `BRSP`.
The ROM_EXT will acknowledge this request with the following message:

```
mode: BRSP
ok: receive boot_svc response via xmodem-crc
```

The ROM_EXT will then transmit the boot services response data structure to the user via the Xmodem-CRC protocol.
After completing this action, the ROM_EXT will switch back to firmware rescue mode.


#### Send an Owner Block (`OWNR`)

The user may request to send an Owner Block to the ROM_EXT with the 4-byte code `OWNR`.
The ROM_EXT will acknowledge this request with the following message:

```
mode: OWNR
ok: send owner_block via xmodem-crc
```

The ROM_EXT will then will prompt for the transfer to start by sending the Xmodem-CRC start character (which is the ASCII character `C`).
After completing this action, the ROM_EXT will switch back to firmware rescue mode.

Note: the ROM_EXT will only accept the Owner Block if the chip is in an ownership transfer state and the receive owner block meets all validity criteria.

#### Request a Reboot (`REBO`)

The user may request a reboot operation with the 4-byte code `REBO`.

The ROM_EXT will acknowledge this request with the following message:

```
mode: REBO
ok: reboot
```

The ROM_EXT will then exit rescue mode and reboot the chip.

### Error Conditions

#### Bad Mode

A bad mode request will result in the following message:

```
mode: <4-byte code>
error: unrecognized mode
```

The current rescue mode will remain unchanged.

#### Xmodem-CRC errors

The following errors and error responses can occur during Xmodem-CRC.
- An invalid start-of-packet: the transfer is aborted.
- An invalid block number: the transfer is cancelled.
- An invalid CRC checksum: the frame is NAKed and the sender should retry the frame.
