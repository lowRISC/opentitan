---
title: "SRAM Controller Technical Specification"
---


# Overview

This document specifies the functionality of the SRAM memory controller.
The SRAM controller is a module that is a peripheral on the chip interconnect bus, and thus follows the [Comportability Specification]({{< relref "doc/rm/comportability_specification" >}}).


The SRAM controller contains the SRAM data and address scrambling device and provides CSRs for controlling the scrambling mechanism, report ECC errors and configure SRAM macro attributes.

## Features

- Lightweight memory and address scrambling based on a reduced-round PRINCE block cipher (see also [prim_prince]({{< relref "hw/ip/prim/doc/prim_prince" >}})).
- Reporting for uncorrectable and correctable integrity errors.
- Exposure of SRAM macro attributes such as write/read margin bits

# Theory of Operations

### Block Diagram

**TODO: draw block diagram and add description**

![SRAM Controller Block Diagram](sram_ctrl_blockdiag.svg)

## Hardware Interfaces

### Parameters

The following table lists the instantiation parameters of the SRAM controller.

Parameter                   | Default (Max)         | Top Earlgrey | Description
----------------------------|-----------------------|--------------|---------------
`Depth`                     | 512                   | multiple     | SRAM depth, needs to be a power of 2 if `NumAddrScrRounds` > 0.
`Width`                     | 32 (64)               | 32           | Effective SRAM width without redundancy.
`CfgWidth`                  | 8                     | 8            | Width of SRAM attributes field.
`NumPrinceRoundsHalf`       | 2 (5)                 | 2            | Number of PRINCE half-rounds.
`NumByteScrRounds`          | 2                     | 2            | Number of intra-byte diffusion rounds, set to 0 to disable.
`NumAddrScrRounds`          | 2                     | 2            | Number of address scrambling rounds, set to 0 to disable.

### Signals

{{< hwcfg "hw/ip/sram_ctrl/data/sram_ctrl.hjson" >}}

The table below lists other SRAM controller signals.

Signal                     | Direction        | Type                               | Description
---------------------------|------------------|------------------------------------|---------------
`sram_tl_i`                | `input`          | `tlul_pkg::tl_h2d_t`               | Second TL-UL interface for the SRAM macro (independent from the CSR TL-UL port).
`sram_tl_o`                | `input`          | `tlul_pkg::tl_d2h_t`               | Second TL-UL interface for the SRAM macro (independent from the CSR TL-UL port).
`lc_escalate_en_i`         | `input`          | `lc_ctrl_pkg::lc_tx_t`             | Multibit life cycle escalation enable signal coming from life cycle controller.
`sram_otp_key_o`           | `output`         | `otp_ctrl_pkg::sram_otp_key_req_t` | Key derivation request going to the key derivation inferface of the OTP controller.
`sram_otp_key_i`           | `input`          | `otp_ctrl_pkg::sram_otp_key_rsp_t` | Ephemeral scrambling key coming back from the key derivation inferface of the OTP controller.

#### Lifecycle Escalation Input

If `lc_escalate_en_i` is set to any different value than `lc_ctrl_pkg::Off`, the current scrambling keys are discarded and reset to `'0`.
This mechanism is part of the [life cycle]({{< relref "hw/ip/lc_ctrl/doc" >}}) state scrapping and secret wiping countermeasure triggered by the alert handler.

#### Interface to OTP

The interface to the key derivation interface inside the OTP controller follows a simple req / ack protocol, where the SRAM controller first requests a new ephemeral key by asserting the `sram_otp_key_i.req`.
The OTP controller then fetches entropy from CSRNG and derives an ephemeral key using the SRAM_DATA_KEY_SEED and the PRESENT scrambling data path as described in the [OTP controller spec]({{< relref "hw/ip/otp_ctrl/doc/_index.md#scrambling-datapath" >}}).
Finally, the OTP controller returns a fresh ephemeral key via the response channels (`sram_otp_key_o[*]`, `otbn_otp_key_o`), which complete the req / ack handshake.
The wave diagram below illustrates this process for the OTBN scrambling device.

{{< wavejson >}}
{signal: [
  {name: 'clk_i',                     wave: 'p.......'},
  {name: 'sram_otp_key_o.req',        wave: '01.|..0.'},
  {name: 'otbn_otp_key_i.ack',        wave: '0..|.10.'},
  {name: 'sram_otp_key_i.nonce',      wave: '0..|.30.'},
  {name: 'sram_otp_key_i.key',        wave: '0..|.30.'},
  {name: 'sram_otp_key_i.seed_valid', wave: '0..|.10.'},
]}
{{< /wavejson >}}

If the key seeds have not yet been provisioned in OTP, the keys are derived from all-zero constants, and the `*.seed_valid` signal will be set to 0 in the response.
It should be noted that this mechanism requires the CSRNG and entropy distribution network to be operational, and a key derivation request will block if they are not.

Note that the req/ack protocol runs on `clk_otp_i`.
The SRAM controller synchronizes the data over via a req/ack handshake primitive `prim_sync_reqack.sv` primitive as shown below.

![OTP Key Req Ack](../../otp_ctrl/doc/otp_ctrl_key_req_ack.svg)

Note that the key and nonce output signals on the OTP controller side are guaranteed to remain stable for at least 62 OTP clock cycles after the `ack` signal is pulsed high, because the derivation of a 64bit half-key takes at least two passes through the 31-cycle PRESENT primitive.
Hence, if the SRAM controller clock `clk_i` is faster or in the same order of magnitude as `clk_otp_i`, the data can be directly sampled upon assertion of `src_ack_o`.
If the SRAM controller runs on a significantly slower clock than OTP, an additional register (as indicated with dashed grey lines in the figure) has to be added.

## Design Details

** TODO: add detailed description of scrambling mechanism **

# Programmer's Guide

## Initialization

The memory inside the SRAM controller can be used right away after a system reset.
However, since the scrambling key defaults to all-zero, it is recommended that SW performs the following initialization steps as early in the boot process as possible.

1. (optional) If the physical timing of the SRAM macro needs to be changed from the default, SW should program the correct SRAM attributes to {{< regref "SRAM_CFG" >}}. Note that this is a debug feature, and hence likely not required for normal operation.

2. Lock out write access to the SRAM attributes by clearing {{< regref "SRAM_CFG_REGWEN" >}}.

3. Request a new ephemeral scrambling key from OTP by writing 0x1 to {{< regref "CTRL.RENEW_SCR_KEY" >}} and wait until the SRAM controller sets {{< regref "STATUS.SCR_KEY_VALID" >}} to 0x1. Note that any memory access to the SRAM will error out while a key request is pending.

4. Check the {{< regref "STATUS.SCR_KEY_SEED_VALID" >}} bit:
    - In case the scrambling key seeds have been fully provisioned to OTP, this bit should be set to 0x1. A value of 0x0 indicates that the OTP could be malfunctioning or has been tampered with.
    - If the scrambling seeds have not yet been provisioned to OTP, this bit is set to 0x0. The scrambling key will in that case still be ephemeral, but the key seed mixed in as part of the key derivation process will be statically set to all-zero.

5. (optional) Lock down write access to {{< regref "CTRL.RENEW_SCR_KEY" >}} by writing to {{< regref "CTRL_REGWEN" >}} if future key renewals should be disallowed until the next system reset.

6. (optional) Depending on the SW requirements, the SRAM should be initialized with zero at this point.

Note that before (re-)requesting a new SRAM key it is imperative to make sure that:
- The memory contents are not needed anymore. Requesting a key implicitly wipes all data in the SRAM.
- The CSRNG and the entropy distribution network have been initialized. The key derivation mechanism in OTP needs to request a chunk of fresh entropy, and that request will block until the entropy distribution network responds.

It should also be noted that data and address scrambling is never entirely disabled - even when the default all-zero scrambling key is used.
If the default all-zero key is used, this simply means that the key input to the scrambling device is deterministically set to all-zero.

## Error Handling

Data in the SRAM is integrity protected.
In case a correctable or uncorrectable integrity failure is detected, the SRAM controller raises an `sram_integ_error` interrupt, and sets the {{< regref "STATUS.ERROR" >}} bit in the CSRs.
At the same time, the TL-UL transaction will error out if the error is uncorrectable.

If the {{< regref "STATUS.ERROR" >}} bit is set, software should check the {{< regref "ERROR_TYPE" >}} register in order to determine whether a correctable or uncorrectable error has occurred.
The address of the last integrity error is exposed in the {{< regref "ERROR_ADDRESS" >}} register.
The error condition can then be cleared by writing 0x3 to the {{< regref "ERROR_TYPE" >}} register (this will also clear the {{< regref "STATUS.ERROR" >}} bit).

Note that at this time, the employed memory only implements byte parity due to the construction of the memory scrambling mechanism (ECC would be too costly at the byte level).
This means that all integrity failures are currently uncorrectable ({{< regref "ERROR_TYPE.UNCORRECTABLE" >}}).
The {{< regref "ERROR_TYPE.CORRECTABLE" >}} register has been added for readiness such that ECC could be supported in the future.

## Register Table

{{< registers "hw/ip/sram_ctrl/data/sram_ctrl.hjson" >}}
