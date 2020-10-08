---
title: "SRAM Controller Technical Specification"
---


# Overview

This document specifies the functionality of the SRAM memory controller.
The SRAM controller is a module that is a peripheral on the chip interconnect bus, and thus follows the [Comportability Specification]({{< relref "doc/rm/comportability_specification" >}}).


The SRAM controller is a simple peripheral that provides CSRs for controlling the scrambling mechanism, report ECC errors and configure SRAM macro attributes.
It is intended to be instantiated be instantiated on the top-level alongside the `prim_ram_1p_scr.sv` primitive.

## Features

- Control for PRINCE-based lightweight SRAM scrambling mechanism.
- Reporting for uncorrectable and correctable ECC errors.
- CSRs to drive the SRAM macro attributes.

# Theory of Operations
## Hardware Interfaces

### Parameters

The SRAM controller itself has no instantiation parameters.
Parameters like the SRAM Depth and Width can be set directly in the `prim_ram_1p_scr.sv` primitive.

### Signals

{{< hwcfg "hw/ip/sram_ctrl/data/sram_ctrl.hjson" >}}

The table below lists other OTP controller signals.

Signal                     | Direction        | Type                        | Description
---------------------------|------------------|-----------------------------|---------------
`otp_ast_pwr_seq_o`        | `output`         | `otp_ast_req_t `            | Power sequencing signals going to AST (VDD domain).
`otp_ast_pwr_seq_h_i`      | `input`          | `otp_ast_rsp_t `            | Power sequencing signals coming from AST (VCC domain).
`otp_edn_o`                | `output`         | `otp_edn_req_t`             | Entropy request to the entropy distribution network for LFSR reseeding and ephemeral key derivation.
`otp_edn_i`                | `input`          | `otp_edn_rsp_t`             | Entropy acknowledgment to the entropy distribution network for LFSR reseeding and ephemeral key derivation.
`pwr_otp_i`                | `input`          | `pwrmgr::pwr_otp_req_t`     | Initialization request coming from power manager.
`pwr_otp_o`                | `output`         | `pwrmgr::pwr_otp_rsp_t`     | Initialization response and programming idle state going to power manager.
`lc_otp_program_i`         | `input`          | `lc_otp_program_req_t`      | Life cycle state transition request.
`lc_otp_program_o`         | `output`         | `lc_otp_program_rsp_t`      | Life cycle state transition response.
`lc_otp_token_i`           | `input`          | `lc_otp_token_req_t`        | Life cycle RAW unlock token hashing request.
`lc_otp_token_o`           | `output`         | `lc_otp_token_rsp_t`        | Life cycle RAW unlock token hashing response.
`lc_escalate_en_i`         | `input`          | `lc_ctrl_pkg::lc_tx_t`      | Life cycle escalation enable coming from life cycle controller. This signal moves all FSMs within OTP into the error state and triggers secret wiping mechanisms in the secret partitions.
`lc_provision_en_i`        | `input`          | `lc_ctrl_pkg::lc_tx_t`      | Provision enable qualifier coming from life cycle controller. This signal enables read / write access to the RMA_TOKEN and CREATOR_ROOT_KEY_SHARE0 and CREATOR_ROOT_KEY_SHARE1.
`lc_dft_en_i`              | `input`          | `lc_ctrl_pkg::lc_tx_t`      | Test enable qualifier coming from from life cycle controller. This signals enables the TL-UL access port to the proprietary OTP IP.
`otp_lc_data_o`            | `output`         | `otp_lc_data_t`             | life cycle state output holding the current life cycle state, the value of the transition counter and the tokens needed for life cycle transitions.
`otp_keymgr_key_o`         | `output`         | `keymgr_key_t`              | Key output to the key manager holding CREATOR_ROOT_KEY_SHARE0 and CREATOR_ROOT_KEY_SHARE1.
`flash_otp_key_i`          | `input`          | `flash_otp_key_req_t`       | Key derivation request for FLASH scrambling.
`flash_otp_key_o`          | `output`         | `flash_otp_key_rsp_t`       | Key output holding static scrambling keys derived from FLASH_DATA_KEY_SEED and FLASH_ADDR_KEY_SEED.
`sram_otp_key_i`           | `input`          | `sram_otp_key_req_t[NumSramKeyReqSlots-1:0]` | Array with key derivation requests from SRAM scrambling devices.
`sram_otp_key_o`           | `output`         | `sram_otp_key_rsp_t[NumSramKeyReqSlots-1:0]` | Array with key outputs holding ephemeral scrambling keys derived from SRAM_DATA_KEY_SEED.
`otbn_otp_key_i`           | `input`          | `otbn_otp_key_req_t`                         | Key derivation requests from OTBN DMEM scrambling device.
`otbn_otp_key_o`           | `output`         | `otbn_otp_key_rsp_t`                         | Key output holding ephemeral scrambling key derived from SRAM_DATA_KEY_SEED.
`hw_cfg_o`                 | `output`         | `logic [NumHwCfgBits-1:0]`                   | Output of the HW_CFG partition.

The OTP controller contains various interfaces that connect to other comportable IPs within OpenTitan, and these are briefly explained further below.

#### Interface to Flash Scrambler

The interface to the FLASH scrambling device is a simple req/ack interface that provides the flash controller with the two 128bit keys for data and address scrambling.
The keys are derived from the FLASH_DATA_KEY_SEED and FLASH_ADDR_KEY_SEED values stored in the `SECRET1` partition using the [scrambling primitive]({{< relref "#scrambling-datapath" >}}).
If the key seeds have not yet been provisioned, the keys are derived from all-zero constants.

The keys can be requested as illustrated below:

{{< wavejson >}}
{signal: [
  {name: 'clk_i',                    wave: 'p...........'},
  {name: 'flash_otp_key_i.data_req', wave: '01.|..0.|...'},
  {name: 'flash_otp_key_i.addr_req', wave: '01.|....|..0'},
  {name: 'flash_otp_key_o.data_ack', wave: '0..|.10.|...'},
  {name: 'flash_otp_key_o.addr_ack', wave: '0..|....|.10'},
  {name: 'flash_otp_key_o.key',      wave: '0..|.30.|.40'},
]}
{{< /wavejson >}}

Note that the req/ack protocol runs on the OTP clock.
It is the task of the scrambling device to synchronize the handshake protocol by instantiating the `prim_scr_key_req.sv` primitive as shown below.

![OTP Key Req Ack](sram_ctrl_key_req_ack.svg)

Note that the key and nonce output signals on the OTP controller side are guaranteed to remain stable for at least 62 OTP clock cycles after the `ack` signal is pulsed high, because the derivation of a 64bit half-key takes at least two passes through the 31-cycle PRESENT primitive.
Hence, if the scrambling device clock is faster or in the same order of magnitude as the OTP clock, the data can be directly sampled upon assertion of `src_ack_o`.
If the scrambling device runs on a significantly slower clock than OTP, an additional register (as indicated with dashed grey lines in the figure) has to be added.



[life cycle docs]({{< relref "hw/ip/lc_ctrl/doc" >}}


## Design Details

### Block Diagram

The following is a high-level block diagram that illustrates everything that has been discussed.

![OTP Controller Block Diagram](sram_ctrl_blockdiag.svg)

Each of the partitions P0-P6 has its [own controller FSM]({{< relref "#partition-implementations" >}}) that interacts with the OTP wrapper and the [scrambling datapath]({{< relref "#scrambling-datapath" >}}) to fulfill its tasks.
The partitions expose the address ranges and access control information to the DAI in order to block accesses that go to locked address ranges.
Further, the only two blocks that have (conditional) write access to the OTP are the DAI and the Life Cycle Interface (LCI) blocks.
The partitions  can only issue read transactions to the OTP macro.
Note that the access ranges of the DAI and the LCI are mutually exclusive.
I.e., the DAI can read the life cycle partition but it is not allowed to write to it.
The LCI cannot read the OTP, but is allowed to write to the life cycle partition.

The CSR node on the left side of this diagram connects to the DAI, the OTP partitions (P0-P6) and the OTP wrapper through a gated TL-UL interface.
All connections from the partitions to the CSR node are read-only, and typically only carry a subset of the information available.
E.g., the secret partitions only expose their digest value via the CSRs.

The Key Derivation Interface (KDI) on the bottom right side interacts with the scrambling datapath, the CSRNG and the partition holding the scrambling root keys in order to derive static and ephemeral scrambling keys for FLASH and SRAM scrambling.

The test access gate shown at the top of the block diagram is governed by the life cycle qualification signal `dft_en_i`, which is only enabled during the TEST_UNLOCKED* life cycle states.
Otherwise, test access via this TL-UL window is locked down.

In addition to the blocks mentioned so far, the OTP controller also contains an LFSR timer that creates pseudo-randomly distributed partition check requests, and provides pseudo random data at high bandwidth in the event of a secure erase request due to chip-wide alert escalation.
For security reasons, the LFSR is periodically reseeded with entropy coming from CSRNG.


# Programmer's Guide

## Register Table

{{< registers "hw/ip/sram_ctrl/data/sram_ctrl.hjson" >}}
