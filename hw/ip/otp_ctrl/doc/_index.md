---
title: "OTP Controller Technical Specification"
---


# Overview

This document specifies the functionality of the one time programmable (OTP) memory controller.
The OTP controller is a module that is a peripheral on the chip interconnect bus, and thus follows the [Comportability Specification]({{< relref "doc/rm/comportability_specification" >}}).

The OTP is a module that provides a device with one-time-programming functionality.
The result of this programming is non-volatile, and unlike flash, cannot be reversed.
The OTP functionality is constructed through an open-source OTP controller and a proprietary OTP IP.

The OTP controller provides:
- An open-source abstraction interface that software can use to interact with a proprietary OTP block underneath.
- An open-source abstraction interface that hardware components (for example [life cycle controller]({{< relref "hw/ip/lc_ctrl/doc" >}}) and [key manager]({{< relref "hw/ip/keymgr/doc" >}})) can use to interact with a proprietary OTP block underneath.
- High level logical security protection, such as integrity checks and scrambling of sensitive content.
- Software isolation for when OTP contents are readable and programmable.

The proprietary OTP IP provides:
- Reliable, non-volatile storage.
- Technology-specific redundancy or error correction mechanisms.
- Physical defensive features such as SCA and FI resistance.
- Visual and electrical probing resistance.

Together, the OTP controller and IP provide secure one-time-programming functionality that is used throughout the life cycle (LC) of a device.

## Features

- Multiple logical partitions of the underlying OTP IP
  - Each partition is lockable and integrity checked
  - Integrity digests are stored alongside each logical bank
- Periodic / persistent checks of OTP values
  - Periodic checks of shadowed content vs digests
  - Periodic checks of OTP stored content and shadowed content
  - Persistent checks for immediate errors
- Separate life cycle partition and interface to life cycle controller
  - Supports life cycle functions, but cannot be integrity locked
- Lightweight scrambling of secret OTP partition using a global netlist constant
- Lightweight ephemeral key derivation function for RAM scrambling mechanisms
- Lightweight key derivation function for FLASH scrambling mechanism

## OTP Controller Overview

The functionality of OTP is split into an open-source and a closed-source part, with a clearly defined boundary in between, as illustrated in the simplified high-level block diagram below.

![OTP Controller Overview](otp_ctrl_overview.svg)

It is the task of the open-source controller to provide a common, non-technology specific interface to OTP users with a common register interface and a clearly defined I/O interface to hardware.
The open-source controller implements logical isolation and partitioning of OTP storage that enables users to separate different functions of the OTP into "partitions" with different properties.
Finally, the open-source controller provides a high level of security for specific partitions by provisioning integrity digests for each partition, and scrambling of partitions where required.

The proprietary IP on the other hand translates a common access interface to the technology-specific OTP interface, both for functional and debug accesses (for example register accesses to the macro-internal control structure).

This split implies that every proprietary OTP IP must implement a translation layer from a standardized OpenTitan interface to the module underneath.
It also implies that no matter how the OTP storage or word size may change underneath, the open-source controller must present a consistent and coherent software and hardware interface.
This standardized interface is defined further below, and the wrapper leverages the same [technology primitive mechanism]({{< relref "hw/ip/prim/README.md" >}}) that is employed in other parts of OpenTitan in order to wrap and abstract technology-specific macros (such as memories and clocking cells) that are potentially closed-source.

In order to enable simulation and FPGA emulation of the OTP controller even without access to the proprietary OTP IP, a generalized and synthesizable model of the OTP IP is provided in the form of a [generic technology primitive](https://github.com/lowRISC/opentitan/blob/master/hw/ip/prim_generic/rtl/prim_generic_otp.sv).


# Theory of Operations

Conceptually speaking, the OTP functionality is at a high level split into "front-end" and "back-end".
The "front-end" contains the logical partitions that feed the hardware and software consumer interfaces of the system.
The "back-end" represents the programming interface used by hardware and software components to stage the upcoming values.
The diagram below illustrates this behavioral model.

![OTP Controller Block Diagram](otp_ctrl_behavioral_model.svg)

Note that the front-end contains both buffered and unbuffered partitions.
Buffered partitions are sensed once per power cycle and their contents are stored in registers, whereas unbuffered partitions are read on-demand.
The former are typically partitions that contain data like hardware configuration bits, key material and the life cycle state that need to be always available to the hardware, whereas the latter are large partitions that are accessed infrequently, such as the software configurations.
Values that are programmed into a buffered partition via the programming interface (coupled with read verification) are merely "staged", and do not take effect until the next power cycle.

The sections below describe the operation of various pieces of the OTP controller and how it supports the described functionality.

## Logical Partitions

The OTP is logically separated into partitions that represent different functions.
This means the isolation is virtual and maintained by the OTP controller instead of the underlying OTP IP.

Within each logical partition, there are specific enforceable properties

- Confidentiality via secret partitions
  - This controls whether a particular partition contains secret data.
  - If secret, a partition is not readable by software once locked, and is scrambled in storage.
- Read lockability
  - This controls whether a particular partition disables software readability for later stage software.
  - Some partitions can be locked statically (by computing and storing an associated digest in OTP), others can be read locked at runtime via CSRs.
- Write lockability
  - This controls whether a partition is locked and prevented from future updates.
  - A locked partition is stored alongside a digest to be used later for integrity verification.
- Integrity Verification
  - Once a partition is write-locked by calculating and writing a non-zero [digest]({{< relref "#locking-a-partition" >}}) to it, it can undergo periodic verification (time-scale configurable by software).
This verification takes two forms, partition integrity checks, and storage consistency checks.

Since the OTP is memory-like in nature (it only outputs a certain number of bits per address location), some of the logical partitions are buffered in registers for instantaneous and parallel access by hardware.
This is a critical point, since after power-up, these particular OTP contents are stored in flip flops and sourced to the system.
I.e., buffered partitions are **NOT** directly sourced from the OTP macro itself.
Thus the security of both volatile (OTP controller) and non-volatile (OTP IP) storage becomes important.

### Partition Listing and Description

The OTP controller for OpenTitan contains the seven logical partitions shown below.

{{< snippet "hw/ip/otp_ctrl/doc/otp_ctrl_partitions.md" >}}

Generally speaking, the production life cycle of a device is split into 5 stages "Manufacturing" -> "Calibration and Testing" -> "Provisioning" -> "Mission" -> "RMA".
OTP values are usually programmed during "Calibration and Testing", "Provisioning" and "RMA" stages, as explained below.
A detailed listing of all the items and the corresponding memory map can be found in the [Programmer's Guide]({{< relref "#programmers-guide" >}})) further below.

### Calibration and Test

During this stage, the device is tested for functionality and calibrated to ensure uniformity.
The calibration can focus on a number of things, but usually is centered around adjusting clock, voltage and timing sources to remove process variation.
These calibration values are programmed into the CREATOR_SW_CFG partition, as they are non-secret values meant to be read out by software and programmed into respective peripherals.

Early on during this stage, the various tokens are also programmed into the secret partitions and harvested by the silicon creator.

### Provisioning

During this stage, the device is provisioned with the final firmware and a "unique" seed or identity.
The secret partitions are populated with root secrets and keys that are critical to establishing the device identity.

As part of injecting the final firmware, the stock-keeping-unit-specific hardware and software configurations are also programmed.

### Life Cycle Partition

The life cycle partition is active throughout all stages and hence it is the **ONLY** partition that cannot be locked.
After the device finishes provisioning and goes into production, it must retain the ability to transition back to RMA in case of unexpected failures.

In order to support this transition, the [life cycle state]({{< relref "hw/ip/lc_ctrl/doc" >}}) and counters must always be update-able.

## Locking a Partition

Write access to a partition can be permanently locked when software determines it will no longer make any updates to that partition.
To lock, an integrity constant is calculated and programmed alongside the other data of that partition.
The size of that integrity constant depends on the partition size granule, and is either 32bit or 64bit (see also [Direct Access Memory Map]({{< relref "#direct-access-memory-map" >}})).

Once the "integrity digest" is non-zero, no further updates are allowed.
If the partition is secret, software is in addition no longer able to read its contents (see [Secret Partition description]({{< relref "#secret-vs-nonsecret-partitions" >}})).

Note however, in all partitions, the digest itself is **ALWAYS** readable.
This gives software an opportunity to confirm that the locking operation has proceeded correctly, and if not, scrap the part immediately.

Calculation of the integrity digest depends on whether the partition requires periodic background verification.

### Software Configuration Partitions

The software configuration partitions are used as non-volatile storage for flags, configuration and calibration data.
As such, the contents of this partition are usually consumed once as part of code execution, or moved to another storage compartment somewhere in the design.
For example, the clock calibration values and the LDO calibration values are programmed to the analog sensor top (AST) at startup.

As such, it is not necessary to check periodically at the OTP source.
Instead, software can simply check as part of secure boot and take other measures when these values are programmed into peripherals.

For this partition it is thus the responsibility of software to calculate the integrity digest and program it into the OTP.
It is also reasonable to shadow (parts of) this partition in main memory, and there is not an immediate impact from OTP contents to hardware.

### Hardware Configuration and Secret Partitions

The hardware and secret partitions directly affect downstream hardware.
The contents must go through periodic integrity checks and therefore the stored digest is calculated by hardware when software provides the intent to lock (as opposed to the software partitions where the digest has to be calculated by software).

### Life Cycle Partition

The life cycle partition cannot be locked and will therefore not contain a stored digest.
Note however that only the life cycle controller has access to this partition, i.e., the DAI cannot read nor write from/to the life cycle partition.

## Secret vs Non-Secret Partitions

Non-secret OTP partitions hold data that can be public; or data that has no impact on security.
For example, the current value of lock bits or clock calibration values.
These values are stored in OTP as plaintext.

Secret partitions contain data that are critical to security, for example FLASH scrambling keys, device root secret and unlock tokens.
These values are stored scrambled in OTP, and are descrambled upon read.
The currently employed cipher is PRESENT, as it lends itself well to iterative decomposition, and it is a proven lightweight block cipher (see also [PRESENT Scrambling Primitive]({{< relref "hw/ip/prim/doc/prim_present.md" >}}).
The usage of a block cipher however implies that the secret partitions can only be written in 64bit chunks.

Further, the contents of a particular secret partition are not readable by software once locked (other than the digest which must be always readable); while non-secret partitions are always readable unless read accessibility is explicitly removed by software.

Unfortunately, secret partitions must utilize a global netlist key for the scrambling operation, as there is no other non-volatile storage to store a unique key.


## Partition Checks

### Integrity

Once the appropriate partitions have been locked, the hardware integrity checker employs two integrity checks to verify the content of the volatile buffer registers:

1. All buffered partitions have additional ECC protection (8bit ECC for each 64bit block) that is concurrently monitored.
2. The digest of the partition is recomputed at semi-random intervals and compared to the digest stored alongside the partition.

The purpose of this check is NOT to check between the storage flops and the OTP, but whether the buffer register contents remain consistent with the calculated digest.
This verification is primarily concerned with whether the storage flops have experienced fault attacks.
This check applies to only the HW_CFG and SECRET* partitions.
If a failure is encountered, the OTP controller will send out a `fatal_check_error` alert and reset all of its hardware outputs to their defaults.

### Storage Consistency

This verification ensures the value stored in the buffer registers remain consistent with those in the OTP.
This process re-reads the OTP at semi-random intervals and confirms the value read is the same as the value stored.
Note, given there are integrity checks in parallel, it is not necessary for some partitions to check ALL read contents for consistency.
If there is an integrity digest, only the digest needs to be read; otherwise, all values must be read.


This check applies to LIFE_CYCLE, HW_CFG and SECRET* partitions.
If a failure is encountered, the OTP controller will send out a `fatal_check_error` alert and reset all of its hardware outputs to their defaults.

Note that checks applied to life cycle could cause a failure if life cycle is updated, because life cycle is the only partition that may contain live updates.
The controller hence detects this condition and makes sure that the buffer registers are kept up to date in order to prevent false positives.

### Secret Partition Integrity Checks

Since the secret partitions are stored scrambled, this also implies the integrity digest is calculated over the scrambled form.
In order to balance the amount of buffer registers needed, only the decrypted form of the secret partitions is held in buffer registers.
Hardware calculates the digest by re-scrambling the data before passing it through the digest.


## Power-up and Sense

The OTP controller partition storage must output a specified safe default (it is not always 0 like a blank OTP) upon reset release.
This default output must remain until the OTP controller completes all checks.

The OTP controller reads from the OTP IP.
If the reads pass OTP IP internal checks (for example ECC or redundancy), the partition storage is updated; however the output is still held at the default state via an output mux.
After all read is complete, the OTP controller performs integrity checks on the HW_CFG and SECRET* partitions.
If a partition fails the integrity checks at this point it would signal an initialization error in the status CSR and abort further initialization.

After all integrity checks are complete, the OTP controller releases the output gating and marks outputs as valid.
However, any partition marked with "error" continues to hold its output in the default state.

Once the above steps are complete, the partition storage in buffered registers is not updated again (except for updates to the life cycle partition through the life cycle interface).
I.e., values programmed to OTP via the programming interface will not be visible in buffered registers until after the next power cycle.

At this point, outputs of the partition storage are NOT expected to change unless a periodic check suddenly fails.
When this failure occurs, all outputs are reverted to their default state, and an alert is immediately triggered to the alert handler.
For timing purposes, OTP outputs can be treated as semi-static, as this error event should be rare and exceptional.


## Partition Defaults

Partition defaults are context specific.
For example, a hardware configuration item that locks down specific access should default to "no access".
This ensures that a glitch attack on the OTP cannot easily revert the design to an insecure state.

This hence suggests that when an OTP is all 0's and all 1's, it should, whenever possible, reflect an invalid or inert state in the encoding space of the affected item.
This also implies the reset state of consuming agents (for example key manager and life cycle), should default to invalid / inert state as well.


## Program and Read Ports

As shown previously, the OTP is split into a front and back end.
The back-end interface is primarily used to update OTP contents, and read back for debug and verification purposes.
Despite being a separate functional access port from the logical partitions, the program and read ports are subjected to the same access controls.

When a partition is write-locked, programming accesses are disallowed.
If the partition is secret, read accesses by the back-end interface are also disallowed (except for the digest which must always be readable).
Software can also disable any read accesses to the software configuration partitions via CSR settings to prevent later stage software from reading any content.

The exception to the above is the life cycle partition.
The life cycle controller interface also acts as a "back-end" interface that always has programming access to ensure life cycle state can be advanced.

Note, the program and read ports can conflict with ongoing background storage checks, and the OTP controller arbitrates between these two sides.
An in-progress operation will always be completed.
Afterwards, or when two requests arrive at the same time, the priority is life cycle > programming interface > on-demand read accesses via CSR windows > background checks.


## Programming the OTP

The OTP controller has two programming paths:

1. a functional programming path through software (the program port),
2. Life cycle programming path through hardware.

The functional interface is used to update all partitions except for life cycle.
As mentioned previously, any updates made during the current power cycle are **NOT** reflected in the buffered partitions until the next reboot.

The life cycle interface is used to update the life cycle state and transition counter only.
The commands are issued from the [life cycle controller]({{< relref "hw/ip/lc_ctrl/doc" >}}), and similarly, successful or failed indications are also sent back to the life cycle controller.
Similar to the functional interface, the life cycle controller allows only one update per power cycle, and after a requested transition reverts to an inert state until reboot.

For more details on how the software programs the OTP, please refer to the [Programmer's Guide]({{< relref "#programmers-guide" >}})) further below.


## Hardware Interfaces

### Parameters

The following table lists the instantiation parameters of OTP.
Note that parameters prefixed with `RndCnst` are random netlist constants that need to be regenerated via topgen before the tapeout (typically by the silicon creator).

Parameter                   | Default (Max) | Top Earlgrey | Description
----------------------------|---------------|--------------|---------------
`AlertAsyncOn`              | 2'b11         | 2'b11        |
`RndCnstLfsrSeed`           | (see RTL)     | (see RTL)    | Seed to be used for the internal 40bit partition check timer LFSR. This needs to be replaced by the silicon creator before the tapeout.
`RndCnstLfsrPerm`           | (see RTL)     | (see RTL)    | Permutation to be used for the internal 40bit partition check timer LFSR. This needs to be replaced by the silicon creator before the tapeout.
`RndCnstKey`                | (see RTL)     | (see RTL)    | Random scrambling keys for secret partitions, to be used in the [scrambling datapath]({{< relref "#scrambling-datapath" >}}).
`RndCnstDigestConst`        | (see RTL)     | (see RTL)    | Random digest finalization constants, to be used in the [scrambling datapath]({{< relref "#scrambling-datapath" >}}).
`RndCnstDigestIV`           | (see RTL)     | (see RTL)    | Random digest initialization vectors, to be used in the [scrambling datapath]({{< relref "#scrambling-datapath" >}}).
`RndCnstRawUnlockToken`     | (see RTL)     | (see RTL)    | Global RAW unlock token to be used for the first life cycle transition. See also [conditional life cycle transitions]({{< relref "hw/ip/lc_ctrl/doc/_index.md#conditional-transitions" >}}).

### Signals

{{< hwcfg "hw/ip/otp_ctrl/data/otp_ctrl.hjson" >}}

The table below lists other OTP controller signals.

Signal                       | Direction        | Type                        | Description
-----------------------------|------------------|-----------------------------|---------------
`otp_ast_pwr_seq_o`          | `output`         | `otp_ast_req_t `            | Power sequencing signals going to AST (VDD domain).
`otp_ast_pwr_seq_h_i`        | `input`          | `otp_ast_rsp_t `            | Power sequencing signals coming from AST (VCC domain).
`otp_edn_o`                  | `output`         | `otp_edn_req_t`             | Entropy request to the entropy distribution network for LFSR reseeding and ephemeral key derivation.
`otp_edn_i`                  | `input`          | `otp_edn_rsp_t`             | Entropy acknowledgment to the entropy distribution network for LFSR reseeding and ephemeral key derivation.
`pwr_otp_i`                  | `input`          | `pwrmgr::pwr_otp_req_t`     | Initialization request coming from power manager.
`pwr_otp_o`                  | `output`         | `pwrmgr::pwr_otp_rsp_t`     | Initialization response and programming idle state going to power manager.
`lc_otp_program_i`           | `input`          | `lc_otp_program_req_t`      | Life cycle state transition request.
`lc_otp_program_o`           | `output`         | `lc_otp_program_rsp_t`      | Life cycle state transition response.
`lc_otp_token_i`             | `input`          | `lc_otp_token_req_t`        | Life cycle RAW unlock token hashing request.
`lc_otp_token_o`             | `output`         | `lc_otp_token_rsp_t`        | Life cycle RAW unlock token hashing response.
`lc_escalate_en_i`           | `input`          | `lc_ctrl_pkg::lc_tx_t`      | Life cycle escalation enable coming from life cycle controller. This signal moves all FSMs within OTP into the error state and triggers secret wiping mechanisms in the secret partitions.
`lc_check_byp_en_i`          | `input`          | `lc_ctrl_pkg::lc_tx_t`      | Life cycle partition check bypass signal. This signal causes the life cycle partition to bypass consistency checks during life cycle state transitions in order to prevent spurious consistency check failures.
`lc_creator_seed_sw_rw_en_i` | `input`          | `lc_ctrl_pkg::lc_tx_t`      | Provision enable qualifier coming from life cycle controller. This signal enables SW read / write access to the RMA_TOKEN and CREATOR_ROOT_KEY_SHARE0 and CREATOR_ROOT_KEY_SHARE1.
`lc_seed_hw_rd_en_i`         | `input`          | `lc_ctrl_pkg::lc_tx_t`      | Seed read enable coming from life cycle controller. This signal enables HW read access to the CREATOR_ROOT_KEY_SHARE0 and CREATOR_ROOT_KEY_SHARE1.
`lc_dft_en_i`                | `input`          | `lc_ctrl_pkg::lc_tx_t`      | Test enable qualifier coming from from life cycle controller. This signals enables the TL-UL access port to the proprietary OTP IP.
`otp_lc_data_o`              | `output`         | `otp_lc_data_t`             | Life cycle state output holding the current life cycle state, the value of the transition counter and the tokens needed for life cycle transitions.
`otp_keymgr_key_o`           | `output`         | `keymgr_key_t`              | Key output to the key manager holding CREATOR_ROOT_KEY_SHARE0 and CREATOR_ROOT_KEY_SHARE1.
`flash_otp_key_i`            | `input`          | `flash_otp_key_req_t`       | Key derivation request for FLASH scrambling.
`flash_otp_key_o`            | `output`         | `flash_otp_key_rsp_t`       | Key output holding static scrambling keys derived from FLASH_DATA_KEY_SEED and FLASH_ADDR_KEY_SEED.
`sram_otp_key_i`             | `input`          | `sram_otp_key_req_t[NumSramKeyReqSlots-1:0]` | Array with key derivation requests from SRAM scrambling devices.
`sram_otp_key_o`             | `output`         | `sram_otp_key_rsp_t[NumSramKeyReqSlots-1:0]` | Array with key outputs holding ephemeral scrambling keys derived from SRAM_DATA_KEY_SEED.
`otbn_otp_key_i`             | `input`          | `otbn_otp_key_req_t`                         | Key derivation requests from OTBN DMEM scrambling device.
`otbn_otp_key_o`             | `output`         | `otbn_otp_key_rsp_t`                         | Key output holding ephemeral scrambling key derived from SRAM_DATA_KEY_SEED.
`otp_hw_cfg_o`               | `output`         | `otp_hw_cfg_t`                               | Output of the HW_CFG partition.

The OTP controller contains various interfaces that connect to other comportable IPs within OpenTitan, and these are briefly explained further below.

#### CSRNG Interface

The entropy request interface that talks to CSRNG in order to fetch fresh entropy for ephemeral SRAM scrambling key derivation and the LFSR counters for background checks.
It is comprised of the `otp_edn_o` and `otp_edn_i` signals and follows a req / ack protocol.

See also [CSRNG documentation]({{< relref "hw/ip/csrng/doc" >}}).

#### Power Manager Interface

The power manager interface is comprised of three signals overall: an initialization request (`pwr_otp_i.otp_init`), an initialization done response (`pwr_otp_o.otp_done`) and an idle indicator (`pwr_otp_o.otp_idle`).

The power manager asserts `pwr_otp_i.otp_init` in order to signal to the OTP controller that it can start initialization, and the OTP controller signals completion of the initialization sequence by asserting `pwr_otp_o.otp_done` (the signal will remain high until reset).

The idle indication signal `pwr_otp_o.otp_idle` indicates whether there is an ongoing write operation in the DAI or LCI, and the power manager uses that indication to determine whether a power down request needs to be aborted.

Since the power manager may run in a different clock domain, the `pwr_otp_i.otp_init` signal is synchronized within the OTP controller.
The power manager is responsible for synchronizing the `pwr_otp_o.otp_done` and `pwr_otp_o.otp_idle` signals.

See also [power manager documentation]({{< relref "hw/ip/pwrmgr/doc" >}}).

#### Life Cycle Interfaces

The interface to the life cycle controller can be split into three functional sub-interfaces (state output, state transitions, token hashing), and these are explained in more detail below.
Note that the OTP and life cycle controllers are supposed to be in the same clock domain, hence no additional signal synchronization is required.
See also [life cycle controller documentation]({{< relref "hw/ip/lc_ctrl/doc" >}}) for more details.

##### State, Counter and Token Ouput

After initialization, the life cycle partition contents, as well as the tokens and personalization status is output to the life cycle controller via the `otp_lc_data_o` struct.
The life cycle controller uses this information to determine the life cycle state, and steer the appropriate qualifier signals.
Some of these qualifier signals (`lc_dft_en_i`, `lc_creator_seed_sw_rw_en_i`, `lc_seed_hw_rd_en_i` and `lc_escalate_en_i`) are fed back to the OTP controller in order to ungate testing logic to the OTP macro; enable SW write access to the `SECRET2` partition; enable hardware read access to the root key in the `SECRET2` partition; or to push the OTP controller into escalation state.

A possible sequence for the signals described is illustrated below.
{{< wavejson >}}
{signal: [
  {name: 'clk_i',                           wave: 'p.................'},
  {name: 'otp_lc_data_o.valid',             wave: '0.|...|.1.|...|...'},
  {name: 'otp_lc_data_o.state',             wave: '03|...|...|...|...'},
  {name: 'otp_lc_data_o.count',             wave: '03|...|...|...|...'},
  {name: 'otp_lc_data_o.test_unlock_token', wave: '0.|...|.3.|...|...'},
  {name: 'otp_lc_data_o.test_exit_token',   wave: '0.|...|.3.|...|...'},
  {name: 'otp_lc_data_o.id_state',          wave: '0.|.3.|...|...|...'},
  {name: 'otp_lc_data_o.rma_token',         wave: '0.|.3.|...|...|...'},
  {},
  {name: 'lc_creator_seed_sw_rw_en_i',      wave: '0.|...|...|.4.|...'},
  {name: 'lc_seed_hw_rd_en_i',              wave: '0.|...|...|.4.|...'},
  {name: 'lc_dft_en_i',                     wave: '0.|...|...|.4.|...'},
  {},
  {name: 'lc_escalate_en_i',                wave: '0.|...|...|...|.5.'},
]}
{{< /wavejson >}}

Note that the `otp_lc_data_o.valid` signal is only asserted after the `LIFE_CYCLE`, `SECRET0` and `SECRET2` partitions have successfully initialized, since the life cycle collateral contains information from all three partitions.
The `otp_lc_data_o.id_state` signal is set to `lc_ctrl_pkg::Set` iff the `SECRET2` partition containing the root keys has been locked with a digest.


##### State Transitions

In order to perform life cycle state transitions, the life cycle controller can present the new value of the life cycle state and counter via the programming interface as shown below:

{{< wavejson >}}
{signal: [
  {name: 'clk_i',                      wave: 'p.......'},
  {name: 'lc_otp_program_i.req',       wave: '01.|..0.'},
  {name: 'lc_otp_program_i.state',     wave: '03.|..0.'},
  {name: 'lc_otp_program_i.count',     wave: '03.|..0.'},
  {name: 'lc_otp_program_o.ack',       wave: '0..|.10.'},
  {name: 'lc_otp_program_o.err',       wave: '0..|.40.'},
]}
{{< /wavejson >}}

The request must remain asserted until the life cycle controller has responded.
An error is fatal and indicates that the OTP programming operation has failed.

Note that the new state must not clear any bits that have already been programmed to OTP - i.e., the new state must be incrementally programmable on top of the previous state.
There are hence some implications on the life cycle encoding due to the ECC employed, see [life cycle state encoding]({{< relref "hw/ip/lc_ctrl/doc/_index.md#life-cycle-manufacturing-state-encodings" >}}) for details.

##### Token Hashing

The OTP controller implements a [PRESENT-based one-way function]({{< relref "#scrambling-datapath" >}}) on 128bit to compute the partition digests.
This function is reused for the RAW unlock process (see [life cycle docs]({{< relref "hw/ip/lc_ctrl/doc" >}}) for more info), and can be accessed via `lc_otp_token_i`, `lc_otp_token_o`.
The expected timining is illustrated below:

{{< wavejson >}}
{signal: [
  {name: 'clk_i',                          wave: 'p.......'},
  {name: 'lc_otp_token_i.req',             wave: '01.|..0.'},
  {name: 'lc_otp_token_i.token_input',     wave: '03.|..0.'},
  {name: 'lc_otp_token_o.ack',             wave: '0..|.10.'},
  {name: 'lc_otp_token_o.hashed_token',    wave: '0..|.40.'},
]}
{{< /wavejson >}}

#### Interface to Key Manager

The interface to the key manager is a simple struct that outputs the CREATOR_ROOT_KEY_SHARE0 and CREATOR_ROOT_KEY_SHARE1 keys via `otp_keymgr_key_o` if these secrets have been provisioned and locked (via CREATOR_KEY_LOCK).
Otherwise, this signal is tied to all-zeros.

Since the key manager may run in a different clock domain, key manager is responsible for synchronizing the `otp_keymgr_key_o` signals.

#### Interface to Flash Scrambler

The interface to the FLASH scrambling device is a simple req/ack interface that provides the flash controller with the two 128bit keys for data and address scrambling.

The keys can be requested as illustrated below:

{{< wavejson >}}
{signal: [
  {name: 'clk_i',                      wave: 'p...........'},
  {name: 'flash_otp_key_i.data_req',   wave: '01.|..0.|...'},
  {name: 'flash_otp_key_i.addr_req',   wave: '01.|....|..0'},
  {name: 'flash_otp_key_o.data_ack',   wave: '0..|.10.|...'},
  {name: 'flash_otp_key_o.addr_ack',   wave: '0..|....|.10'},
  {name: 'flash_otp_key_o.key',        wave: '0..|.30.|.40'},
  {name: 'flash_otp_key_o.seed_valid', wave: '0..|.10.|.10'},
]}
{{< /wavejson >}}

The keys are derived from the FLASH_DATA_KEY_SEED and FLASH_ADDR_KEY_SEED values stored in the `SECRET1` partition using the [scrambling primitive]({{< relref "#scrambling-datapath" >}}).
If the key seeds have not yet been provisioned, the keys are derived from all-zero constants, and the `flash_otp_key_o.seed_valid` signal will be set to 0 in the response.

Note that the req/ack protocol runs on the OTP clock.
It is the task of the scrambling device to synchronize the handshake protocol by instantiating the `prim_sync_reqack.sv` primitive as shown below.

![OTP Key Req Ack](otp_ctrl_key_req_ack.svg)

Note that the key and nonce output signals on the OTP controller side are guaranteed to remain stable for at least 62 OTP clock cycles after the `ack` signal is pulsed high, because the derivation of a 64bit half-key takes at least two passes through the 31-cycle PRESENT primitive.
Hence, if the scrambling device clock is faster or in the same order of magnitude as the OTP clock, the data can be directly sampled upon assertion of `src_ack_o`.
If the scrambling device runs on a significantly slower clock than OTP, an additional register (as indicated with dashed grey lines in the figure) has to be added.

#### Interfaces to SRAM and OTBN Scramblers

The interfaces to the SRAM and OTBN scrambling devices follow a req / ack protocol, where the scrambling device first requests a new ephemeral key by asserting the request channel (`sram_otp_key_i[*]`, `otbn_otp_key_i`).
The OTP controller then fetches entropy from CSRNG and derives an ephemeral key using the SRAM_DATA_KEY_SEED and the [PRESENT scrambling data path]({{< relref "#scrambling-datapath" >}}).
Finally, the OTP controller returns a fresh ephemeral key via the response channels (`sram_otp_key_o[*]`, `otbn_otp_key_o`), which complete the req / ack handshake.
The wave diagram below illustrates this process for the OTBN scrambling device.

{{< wavejson >}}
{signal: [
  {name: 'clk_i',                     wave: 'p.......'},
  {name: 'otbn_otp_key_i.req',        wave: '01.|..0.'},
  {name: 'otbn_otp_key_o.ack',        wave: '0..|.10.'},
  {name: 'otbn_otp_key_o.nonce',      wave: '0..|.30.'},
  {name: 'otbn_otp_key_o.key',        wave: '0..|.30.'},
  {name: 'otbn_otp_key_o.seed_valid', wave: '0..|.10.'},
]}
{{< /wavejson >}}

If the key seeds have not yet been provisioned, the keys are derived from all-zero constants, and the `*.seed_valid` signal will be set to 0 in the response.
It should be noted that this mechanism requires the CSRNG and entropy distribution network to be operational, and a key derivation request will block if they are not.

Note that the req/ack protocol runs on the OTP clock.
It is the task of the scrambling device to perform the synchronization as described in the previous subsection on the [flash scrambler interface]({{< relref "#interface-to-flash-scrambler" >}}).

#### Hardware Config Bits

The bits of the HW_CFG partition are output via the `otp_hw_cfg_o` struct.
IPs that consume collateral stored in this partition shall connect to this struct via the topgen feature, and break out the appropriate bits by either accessing the correct index or using the struct fields.
These fields are autogenerated from the memory map items allocated to the HW_CFG partition, and the autogenerated struct type can be found in the `otp_ctrl_part_pkg.sv` package.
Note that it is the task of the receiving IP to synchronize these bits accordingly to the local clock.
For convenience, a valid bit is also available in that struct.
The valid bit indicates that the HW_CFG partition has initialized.

## Design Details

### Block Diagram

The following is a high-level block diagram that illustrates everything that has been discussed.

![OTP Controller Block Diagram](otp_ctrl_blockdiag.svg)

Each of the partitions P0-P6 has its [own controller FSM]({{< relref "#partition-implementations" >}}) that interacts with the OTP wrapper and the [scrambling datapath]({{< relref "#scrambling-datapath" >}}) to fulfill its tasks.
The partitions expose the address ranges and access control information to the DAI in order to block accesses that go to locked address ranges.
Further, the only two blocks that have (conditional) write access to the OTP are the DAI and the Life Cycle Interface (LCI) blocks.
The partitions can only issue read transactions to the OTP macro.
Note that the access ranges of the DAI and the LCI are mutually exclusive.
I.e., the DAI cannot read from nor write to the life cycle partition.
The LCI cannot read the OTP, but is allowed to write to the life cycle partition.

The CSR node on the left side of this diagram connects to the DAI, the OTP partitions (P0-P6) and the OTP wrapper through a gated TL-UL interface.
All connections from the partitions to the CSR node are read-only, and typically only carry a subset of the information available.
E.g., the secret partitions only expose their digest value via the CSRs.

The Key Derivation Interface (KDI) on the bottom right side interacts with the scrambling datapath, the CSRNG and the partition holding the scrambling root keys in order to derive static and ephemeral scrambling keys for FLASH and SRAM scrambling.

The test access gate shown at the top of the block diagram is governed by the life cycle qualification signal `dft_en_i`, which is only enabled during the TEST_UNLOCKED* life cycle states.
Otherwise, test access via this TL-UL window is locked down.

In addition to the blocks mentioned so far, the OTP controller also contains an LFSR timer that creates pseudo-randomly distributed partition check requests, and provides pseudo random data at high bandwidth in the event of a secure erase request due to chip-wide alert escalation.
For security reasons, the LFSR is periodically reseeded with entropy coming from CSRNG.

### Data Allocation and Packing
#### Software View

The effective word width of an OTP IP typically depends on a couple of factors, including the redundancy scheme employed.
For this the design at hand, it is assumed that this native OTP word-width is 16bit.
For software convenience, however, these details are abstracted and the open-source OTP controller exposes the OTP storage as a linear address space of 32bit words, which is aligned with the machine word size of the Ibex processor.
Since the OTP IP employs a redundancy mechanism similar to ECC, this implies however that write operations take place at a granularity of 32bit blocks for non-secret and 64bit blocks for secret partitions (due to the scrambling).
Hence, software is responsible to appropriately pack and program items, since each 32bit location can only be programmed once.

#### Life Cycle View

Since the life cycle partition is the only partition that needs live updates in-field, proper care must be taken to properly encode data in this partition such that incremental updates are possible.
The life cycle state is hence encoded such that incremental updates to the state are always carried out at the granularity of a 16bit word.
Further, the life cycle transition counter is encoded such that each stroke consumes a full 16bit word for the same reason.

See [life cycle controller documentation]({{< relref "hw/ip/lc_ctrl/doc" >}}) for more details on the life cycle encoding.

### Partition Controllers

In RTL, we distinguish between buffered and unbuffered partition modules.
These are parameterized, such that we can assemble the array of OTP partitions with these two modules only.
The corresponding controller FSMs are explained in more detail below.

#### Unbuffered Partition

![Unbuffered Partition FSM](otp_ctrl_unbuf_part_fsm.svg)

As shown above, the unbuffered partition module has a relatively simple controller FSM that only reads out the digest value of the partition upon initialization, and then basically waits for TL-UL read transactions to its corresponding window in the CSR space.

Write access through the DAI will be locked in case the digest is set to a non-zero value.
Also, read access through the DAI and the CSR window can be locked at runtime via a CSR.
Read transactions through the CSR window will error out if they are out of bounds, or if read access is locked.

Note that unrecoverable [OTP errors]({{< relref "#generalized-open-source-interface" >}}) or ECC failures in the digest register will move the partition controller into a terminal error state.

#### Buffered Partition

![Buffered Partition FSM](otp_ctrl_buf_part_fsm.svg)

The controller FSM of the buffered partition module is more complex than the unbuffered counterpart, since it has to account for scrambling and digest calculation.

Upon initialization, the controller reads out the whole partition and descrambles it on the fly if needed.

Then, right after the initial readout, the partition controller jumps into the first integrity check, which behaves somewhat differently, depending on whether the partition is digest protected (or not) and/or scrambled (or not).
If the partition is not digest protected, or if the digest has not yet been computed, the check completes right away, and the buffered values are released for hardware broadcast.
Otherwise, the partition contents in the buffer registers are re-scrambled if needed, and a digest is computed on the fly.
If the computed digest matches with the one that has been read out before, the buffered registers are released for hardware broadcast.
Otherwise, the buffered values are gated to their default, and an alert is triggered through the error handling logic.

After initialization, the integrity check (as described above) and the consistency check can be triggered by the LFSR timer mechanism on a periodic basis.

The consistency check behaves differently, depending on whether the partition is digest protected or not.
If it is, the consistency check will read out the digest stored in OTP and compare it with the value stored in the buffer register.
Otherwise, if no digest is available, the controller will read out the whole partition from OTP, and compare it to the contents stored in the buffer registers.
In case of a mismatch, the buffered values are gated to their default, and an alert is triggered through the error handling logic.

Note that in case of unrecoverable OTP errors or ECC failures in the buffer registers, the partition controller FSM is moved into a terminal error state, which locks down all access through DAI and clamps the values that are broadcast in hardware to their defaults.

### Direct Access Interface Control

![Direct Access Interface FSM](otp_ctrl_dai_fsm.svg)

Upon reset release, the DAI controller first sends an initialization command to the OTP macro.
Once the OTP macro becomes operational, an initialization request is sent to all partition controllers, which will read out and initialize the corresponding buffer registers.
The DAI then becomes operational once all partitions have initialized, and supports read, write and digest calculation commands (see [here]({{< relref "#direct-access-interface" >}}) for more information about how to interact with the DAI through the CSRs).

Read and write commands transfer either 32bit or 64bit of data from the OTP to the corresponding CSR and vice versa. The access size is determined automatically, depending on whether the partition is scrambled or not. Also, (de)scrambling is performed transparently, depending on whether the partition is scrambled or not.

Digest calculation commands read out the complete contents of a particular partition, compute a digest and write that digest value to the predefined location at the end of the partition.

Note that any unrecoverable OTP error will move the DAI into a terminal error state, where all access through the DAI will be locked.
Also, the DAI consumes the read and write access information provided by the partition controller, and if a certain read or write access is not permitted, a recoverable error will be flagged in the status / error CSRs.

### Life Cycle Interface Control

![Life Cycle Interface FSM](otp_ctrl_lci_fsm.svg)

Upon reset release the LCI FSM waits until the OTP controller has initialized and the LCI gets enabled.
Once it is in the idle state, life cycle state updates can be initiated via the life cycle interface as [described here]({{< relref "#state-transitions" >}}).
The LCI controller takes the life cycle state to be programmed and writes all 16bit words to OTP.
In case of unrecoverable OTP errors, the FSM signals an error to the life cycle controller and moves into a terminal error state.

### Key Derivation Interface

![Key Derivation Interface FSM](otp_ctrl_kdi_fsm.svg)

Upon reset release the KDI FSM waits until the OTP controller has initialized and the KDI gets enabled.
Once it is in the idle state, key derivation and token hashing can be requested via the [token hashing]({{< relref "#token-hashing" >}}), [flash]({{< relref "#interface-to-flash-scrambler" >}}) and [sram]({{< relref "#interface-to-sram-and-otbn-scramblers" >}}) interfaces.
Based on which interface makes the request, the KDI controller will evaluate a variant of the PRESENT digest mechanism as described in more detail below.

### Scrambling Datapath

![OTP Digest Mechanism](otp_ctrl_digest_mechanism.svg)

The scrambling datapath is built around an iterative implementation of the [PRESENT lightweight cipher]({{< relref "hw/ip/prim/doc/prim_present" >}}) that performs one round per cycle.
The datapath contains some additional multiplexing circuitry to enable the DAI, KDI and partition controllers to evaluate different functions with the same datapath.
The algorithmic steps of these functions are explained in more detail below.

#### Scrambling

As illustrated in subfigure a) in the diagram above, the standard 128bit-key PRESENT configuration with 31 rounds is used for scrambling operations.
The key used for scrambling is a global netlist constant chosen by the silicon creator, and all secret partitions are encrypted using the their own distinct netlist constant.
Note that the amount of data that is being scrambled is small (160byte = 20 x 64bit blocks) and the scrambled data remains constant.
Hence, no additional masking or diversification scheme is applied since only a very limited amount of information can be gathered by observing the scrambling operation via side-channels.

#### Digest Calculation

The integrity digests used in the [partition checks]({{< relref "#partition-checks" >}}) are computed using a custom [Merkle-Damgard](https://en.wikipedia.org/wiki/Merkle%E2%80%93Damg%C3%A5rd_construction) scheme, where the employed one-way compression function F is constructed by using PRESENT in a [Davies-Meyer arrangement](https://en.wikipedia.org/wiki/One-way_compression_function#Davies%E2%80%93Meyer).
This is illustrated in subfigure b).

At the beginning of the digest calculation the 64bit state is initialized with an initialization vector (IV).
Then, the data to be digested is split into 128bit chunks, each of which is used as a 128bit key input for updating the 64bit state with the compression function F.
Chunks that are not aligned with 128bit are padded with zero, and the finalization operation consists of another 31-round encryption pass with a finalization constant.
Note that both the IV as well as the finalization constant are global netlist constants chosen by the silicon creator.

#### Unlock Token Hashing

The unlock hashing function is used by the life cycle controller to pass the RAW unlock token through a one-way function before performing the actual token comparison with the netlist constant.
This makes it harder to reverse engineer and break the RAW unlock process since in addition to extracting the hashed RAW unlock token, an attacker would have to invert the one-way function (or find a collision).
The hash process is similar to the digest calculation, and uses the PRESENT primitive in a Merkle-Damgard construction to reduce the 128bit token into two 64bit hash-halves as illustrated in subfigure c).


Due the PRESENT primitive being a 64bit cipher, the hash produced in this manner is essentially 64bit in strength, which would make the two 64bit halves susceptible to brute-force collision attacks if they where computed completely independently.
To that end, the second 64bit halve is computed in a chained way by using the first 64bit halve as IV input.

#### Scrambling Key Derivation

The key derivation functions for ephemeral SRAM and static FLASH scrambling keys employ a similar construction as the digest calculation and token hashing functions.
In particular, the keys are derived by repeatedly reducing a (partially random) block of data into a 64bit block, as illustrated in subfigures d) and e).

For ephemeral SRAM scrambling keys, the data block is composed of the 128bit SRAM_DATA_KEY_SEED stored in OTP, as well as 128bit of fresh entropy fetched from the CSRNG.
This process is repeated twice in order to produce a 128bit key.

For static FLASH scrambling keys, the data block is composed of a 128bit part of either the FLASH_DATA_KEY_SEED or the FLASH_ADDR_KEY_SEED stored in OTP.
These key seeds are 256bit in size, allowing to use a unique chunk of 128bit of key seed data to derive a 64bit halve of a particular scrambling key.

Note that the IV and finalization constants are distinct for SRAM and FLASH data and FLASH address scrambling keys.
These constants are chosen by the silicon creator prior to the tapeout.

### Access Arbitration

Access to the OTP wrapper and the scrambling datapath are both round-robin arbitrated, where the former arbitration occurs at cycle level (i.e., individual OTP memory accesses), and the latter occurs at the level of complete transactions (i.e., full digest or encryption).
Arbitration at transaction level is implemented similarly to cycle-based arbitration, with the difference that the grant signals remain asserted until the requestor deasserts the request (thereby releasing the arbiter, which acts as a mutex in this case).
This is behavior illustrated in the example below.

{{< wavejson >}}
{signal: [
  {name: 'clk_i',                  wave: 'p............'},
  {name: 'part_scrmbl_mtx_req[0]', wave: '01....0.1....'},
  {name: 'part_scrmbl_mtx_req[1]', wave: '0.1......0...'},
  {name: 'part_scrmbl_mtx_req[2]', wave: '0.1........0.'},
  {},
  {name: 'part_scrmbl_mtx_gnt[0]', wave: '01....0....1.'},
  {name: 'part_scrmbl_mtx_gnt[1]', wave: '0.....1..0...'},
  {name: 'part_scrmbl_mtx_gnt[2]', wave: '0........1.0.'},
]}
{{< /wavejson >}}

### Primitive Wrapper and FPGA Emulation

![OTP Wrapper Block Diagram](otp_ctrl_prim_otp.svg)

The OTP IP is wrapped up in a primitive wrapper that exposes a TL-UL interface for testing purposes, and a generalized open-source interface for functional operation (described below).
Any OTP redundancy mechanism like per-word ECC is assumed to be handled inside the wrapper, which means that the word width exposed as part of the generalized interface is the effective word width.

Note that the register space exposed via the TL-UL interface is dependent on the underlying proprietary OTP IP and hence not further described in this document.

#### Generalized Open-source Interface

The generalized open-source interface uses a couple of parameters (defaults set for Earlgrey configuration).

Parameter      | Default | Top Earlgrey  | Description
---------------|---------|---------------|---------------
`Width`        | 16      | 16            | Native OTP word width.
`Depth`        | 1024    | 1024          | Depth of OTP macro.
`CmdWidth`     | 2       | 2             | Width of the OTP command.
`ErrWidth`     | 3       | 3             | Width of error code output signal.
`PwrSeqWidth`  | 2       | 2             | Width of power sequencing signals to/from AST.
`SizeWidth`    | 2       | 2             | Width of the size field.
`IfWidth`      | 2^`SizeWidth` * `Width` | 2^`SizeWidth` * `Width` | Data interface width.

The generalized open-source interface is a simple command interface with a ready / valid handshake that makes it possible to introduce back pressure if the OTP macro is not able to accept a command due to an ongoing operation.

In order to facilitate the scrambling and digest operations, the data width has been sized such that data blocks up to the PRESENT block size (64bit) can be transferred across the generalized interface. The actual size of a transfer is determined via the size_i field. Transfer sizes are specified in multiples of the native OTP block size, as listed below.

Value of `size_i` | #Native OTP Words | Bit Slice
------------------|-------------------|------------
2'b00             |                 1 | `{word0} = data[15:0]`
2'b01             |                 2 | `{word1, word0} = data[31:0]`
2'b10             |                 3 | `{word2, word1, word0} = data[47:0]`
2'b11             |                 4 | `{word3, word2, word1, word0} = data[63:0]`

Responses are returned in-order via an unidirectional response interface (i.e., without back pressure capability).
Downstream logic must be able to sink the response in any case.
The response optionally carries read data, depending on whether the operation that took place was a read or not.
Also, an error signal returns a non-zero error code in case an error occurred while carrying out the OTP command.

Signal                  | Direction        | Type                        | Description
------------------------|------------------|-----------------------------|---------------
`pwr_seq_o`             | `output`         | `logic`                     | Power sequencing signals to AST (on VDD domain).
`pwr_seq_h_i`           | `input`          | `logic`                     | Power sequencing signals from AST (on VCC domain).
`ready_o`               | `output`         | `logic`                     | Ready signal for the command handshake.
`valid_i`               | `input`          | `logic`                     | Valid signal for the command handshake.
`size_i`                | `input`          | `logic [SizeWidth-1:0]`     | Number of native OTP words to transfer, minus one: `2'b00 = 1 native word` ... `2'b11 = 4 native words`.
`cmd_i`                 | `input`          | `logic [CmdWidth-1:0]`      | OTP command: `2'b00 = read`, `2'b01 = write`, `2'b11 = initialize`
`addr_i`                | `input`          | `logic [$clog2(Depth)-1:0]` | OTP word address.
`wdata_i`               | `input`          | `logic [IfWidth-1:0]`       | Write data for write commands.
`valid_o`               | `output`         | `logic`                     | Valid signal for command response.
`rdata_o`               | `output`         | `logic [IfWidth-1:0]`       | Read data from read commands.
`err_o`                 | `output`         | `logic [ErrWidth-1:0]`      | Error code.

The `prim_otp` wrappers implements the `Macro*` error codes (0x0 - 0x4) defined in the [OTP error handling]({{< relref "#error-handling" >}}).

The timing diagram below illustrates the timing of a command.
Note that both read and write commands return a response, and each command is independent of the previously issued commands.
The latency from accepting a command to returning a response depends on the underlying OTP IP and is typically larger than 10 cycles.
The returned values depend on the command type and whether an error occurred or not.

{{< wavejson >}}
{
  signal: [
    { name: 'clk_i',    wave: 'p.............' },
    { name: 'ready_o',  wave: '0..10|.10.|...' , node: '...a...c'},
    { name: 'valid_i',  wave: '01..0|1.0.|...' },
    { name: 'size_i',   wave: '03..0|3.0.|...' },
    { name: 'cmd_i',    wave: '04..0|4.0.|...' },
    { name: 'wdata_i',  wave: '05..0|5.0.|...' },
    { name: 'valid_o',  wave: '0....|..10|.10' , node: '........b...d'},
    { name: 'rdata_o',  wave: '0....|..50|.50' },
    { name: 'err_o',    wave: '0....|..40|.40' },
  ],
  edge: [
   'a~>b',
   'c~>d',
  ],
  head: {
    text: 'Timing of an OTP command.',
  },
  foot: {
    text: "Cmd's are accepted in cycles 3/7, and the corresponding responses return in cycles 8/12.",
    tick: 0,
  }
}
{{< /wavejson >}}

Note that the open source OTP controller allows up to two outstanding OTP commands, meaning that it is permissible to acknowledge an incoming command and start working on it while the results of the last command are still in the process of being output (e.g., due to an output register stage).

#### Generic Simulation and FPGA Emulation Model

For open-source simulation and FPGA emulation, a synthesizable and generic OTP wrapper module is provided (`prim_generic_otp`).
This is automatically selected in the OpenTitan build flow via the technology primitive mechanism if no proprietary OTP IP is available for a specific technology.
The OTP storage in `prim_generic_otp` is emulated using a standard RAM primitive `prim_generic_ram_1p`.
While this storage element is volatile, the primitive is constructed such that the contents are not wiped upon a system-wide reset.
I.e., only a power-cycle wipes the RAM primitive, thereby enabling limited emulation of the OTP function and life cycle transitions also on an FPGA device.


# Programmer's Guide

During provisioning and manufacturing, SW interacts with the OTP controller mostly through the Direct Access Interface (DAI), which is described below.
Afterwards during production, SW is expected to perform only read accesses via the exposed CSRs and CSR windows, since all write access to the partitions has been locked down.

The following sections provide some general guidance, followed by an explanation of the DAI and a detailed OTP memory map.
Typical programming sequences are explained at the end of the Programmer's guide.

## General Guidance

### Initialization

The OTP controller initializes automatically upon power-up and is fully operational by the time the processor boots.
The only initialization steps that SW should perform are:

1. Check that the OTP controller has successfully initialized by reading {{< regref STATUS >}}. I.e., make sure that none of the ERROR bits are set, and that the DAI is idle ({{< regref STATUS.DAI_IDLE >}}).
2. Set up the periodic background checks:
    - Choose whether to enable periodic [background checks]({{< relref "#partition-checks" >}}) by programming nonzero mask values to {{< regref INTEGRITY_CHECK_PERIOD >}} and {{< regref CONSISTENCY_CHECK_PERIOD >}}.
    - Choose whether such checks shall be subject to a timeout by programming a nonzero timeout cycle count to {{< regref CHECK_TIMEOUT >}}.
    - It is recommended to lock down the background check registers via {{< regref CHECK_REGWEN >}}, once the background checks have been set up.

If needed, one-off integrity and consistency checks can be triggered via {{< regref CHECK_TRIGGER >}}.
If this functionality is not needed, it is recommended to lock down the trigger register via {{< regref CHECK_TRIGGER_REGWEN >}}.

Later on during the boot process, SW may also choose to block read access to the CREATOR_SW_CFG or OWNER_SW_CFG partitions at runtime via {{< regref CREATOR_SW_CFG_READ_LOCK >}} and {{< regref OWNER_SW_CFG_READ_LOCK >}}.


### Reset Considerations

It is important to note that values in OTP **can be corrupted** if a reset occurs during a programming operation.
This should be of minor concern for SW, however, since all partitions except for the LIFE_CYCLE partition are being provisioned in secure and controlled environments, and not in the field.
The LIFE_CYCLE partition is the only partition that is modified in the field - but that partition is entirely owned by the life cycle controller and not by SW.

### Programming Already Programmed Regions

OTP words cannot be programmed twice, and doing so may damage the memory array.
Hence the OTP controller performs a blank check and returns an error if a write operation is issued to an already programmed location.

### Potential Side-Effects on Flash via Life Cycle

It should be noted that the locked status of the partition holding the creator root key (i.e., the value of the {{< regref "SECRET2_DIGEST_0" >}}) determines the ID_STATUS of the device, which in turn determines SW accessibility of creator seed material in flash and OTP.
That means that creator-seed-related collateral needs to be provisioned to Flash **before** the OTP digest lockdown mechanism is triggered, since otherwise accessibility to the corresponding flash region is lost.
See the [life cycle controller documentation]({{< relref "hw/ip/lc_ctrl/doc/_index.md#id-state-of-the-device" >}}) for more details.

## Direct Access Interface

OTP has to be programmed via the Direct Access Interface, which is comprised of the following CSRs:

CSR Name                             | Description
-------------------------------------|------------------------------------
{{< regref DIRECT_ACCESS_WDATA_0 >}} | Low 32bit word to be written.
{{< regref DIRECT_ACCESS_WDATA_1 >}} | High 32bit word to be written.
{{< regref DIRECT_ACCESS_RDATA_0 >}} | Low 32bit word that has been read.
{{< regref DIRECT_ACCESS_RDATA_1 >}} | High 32bit word that has been read.
{{< regref DIRECT_ACCESS_ADDRESS >}} | byte address for the access.
{{< regref DIRECT_ACCESS_CMD >}}     | Command register to trigger a read or a write access.
{{< regref DIRECT_ACCESS_REGWEN >}}  | Write protection register for DAI.

See further below for a detailed [Memory Map]({{< relref "#direct-access-memory-map" >}}) of the address space accessible via the DAI.

### Readout Sequence

A typical readout sequence looks as follows:

1. Check whether the DAI is idle by reading the {{< regref STATUS >}} register.
2. Write the byte address for the access to {{< regref DIRECT_ACCESS_ADDRESS >}}.
Note that the address is aligned with the granule, meaning that either 2 or 3 LSBs of the address are ignored, depending on whether the access granule is 32 or 64bit.
3. Trigger a read command by writing 0x1 to {{< regref DIRECT_ACCESS_CMD >}}.
4. Poll the {{< regref STATUS >}} until the DAI state goes back to idle.
Alternatively, the `otp_operation_done` interrupt can be enabled up to notify the processor once an access has completed.
5. If the status register flags a DAI error, additional handling is required (see [Section on Error handling]({{< relref "#error-handling" >}})).
6. If the region accessed has a 32bit access granule, the 32bit chunk of read data can be read from {{< regref DIRECT_ACCESS_RDATA_0 >}}.
If the region accessed has a 64bit access granule, the 64bit chunk of read data can be read from the {{< regref DIRECT_ACCESS_RDATA_0 >}} and {{< regref DIRECT_ACCESS_RDATA_1 >}} registers.
7. Go back to 1. and repeat until all data has been read.

Note that the hardware will set {{< regref DIRECT_ACCESS_REGWEN >}} to 0x0 while an operation is pending in order to temporarily lock write access to the CSRs registers.

### Programming Sequence

A typical programming sequence looks as follows:

1. Check whether the DAI is idle by reading the {{< regref STATUS >}} register.
2. If the region to be accessed has a 32bit access granule, place a 32bit chunk of data into {{< regref DIRECT_ACCESS_WDATA_0 >}}.
If the region to be accessed has a 64bit access granule, both the {{< regref DIRECT_ACCESS_WDATA_0 >}} and {{< regref DIRECT_ACCESS_WDATA_1 >}} registers have to be used.
3. Write the byte address for the access to {{< regref DIRECT_ACCESS_ADDRESS >}}.
Note that the address is aligned with the granule, meaning that either 2 or 3 LSBs of the address are ignored, depending on whether the access granule is 32 or 64bit.
4. Trigger a write command by writing 0x2 to {{< regref DIRECT_ACCESS_CMD >}}.
5. Poll the {{< regref STATUS >}} until the DAI state goes back to idle.
Alternatively, the `otp_operation_done` interrupt can be enabled up to notify the processor once an access has completed.
6. If the status register flags a DAI error, additional handling is required (see [Section on Error handling]({{< relref "#error-handling" >}})).
7. Go back to 1. and repeat until all data has been written.

Note that the hardware will set {{< regref DIRECT_ACCESS_REGWEN >}} to 0x0 while an operation is pending in order to temporarily lock write access to the CSRs registers.

### Digest Calculation Sequence

The hardware digest computation for the hardware and secret partitions can be triggered as follows:

1. Check whether the DAI is idle by reading the {{< regref STATUS >}} register.
3. Write the partition base address to {{< regref DIRECT_ACCESS_ADDRESS >}}.
4. Trigger a digest calculation command by writing 0x4 to {{< regref DIRECT_ACCESS_CMD >}}.
5. Poll the {{< regref STATUS >}} until the DAI state goes back to idle.
Alternatively, the `otp_operation_done` interrupt can be enabled up to notify the processor once an access has completed.
6. If the status register flags a DAI error, additional handling is required (see [Section on Error handling]({{< relref "#error-handling" >}})).

Note that the hardware will set {{< regref DIRECT_ACCESS_REGWEN >}} to 0x0 while an operation is pending in order to temporarily lock write access to the CSRs registers.

## Error Handling

The agents that can access the OTP macro (DAI, LCI, buffered/unbuffered partitions) expose detailed error codes that can be used to root cause any failure.
The error codes are defined in the table below, and the corresponding `otp_err_e` enum type can be found in the `otp_ctrl_pkg`.
The table also lists which error codes are supported by which agent.

Errors that are not "recoverable" are severe errors that move the corresponding partition or DAI/LCI FSM into a terminal error state, where no more commands can be accepted (a system reset is required to restore functionality in that case).
Errors that are "recoverable" are less severe and do not cause the FSM to jump into a terminal error state.

Note that error codes that originate in the physical OTP macro are prefixed with `Macro*`.

Error Code | Enum Name            | Recoverable | DAI | LCI | Unbuf | Buf   | Description
-----------|----------------------|-------------|-----|-----|-------|-------|-------------
0x0        | NoError              | -           |  x  |  x  |   x   |  x    | No error has occurred.
0x1        | MacroError           | no          |  x  |  x  |   x   |  x    | Returned if the OTP macro command was invalid or did not complete successfully due to a macro malfunction.
0x2        | MacroEccCorrError    | yes         |  x  |  -  |   x   |  x    | A correctable ECC error has occurred during a read operation in the OTP macro.
0x3        | MacroEccUncorrError  | no          |  x  |  -  |   x   |  x    | An uncorrectable ECC error has occurred during a read operation in the OTP macro.
0x4        | MacroWriteBlankError | yes         |  x  |  x  |   x   |  x    | This error is returned if a write operation attempted to clear an already programmed bit location.
0x5        | AccessError          | yes         |  x  |  -  |   x   |  -    | An access error has occurred (e.g. write to write-locked region, or read to a read-locked region).
0x6        | CheckFailError       | no          |  -  |  -  |   x   |  x    | An unrecoverable ECC, integrity or consistency error has been detected.
0x7        | FsmStateError        | no          |  x  |  x  |   x   |  x    | The FSM has been glitched into an invalid state, or escalation has been triggered and the FSM has been moved into a terminal error state.

All non-zero error codes listed above trigger an `otp_error` interrupt.
In addition, all unrecoverable OTP `Macro*` errors (codes 0x1, 0x3) trigger a `fatal_macro_error` alert, while all remaining unrecoverable errors trigger a `fatal_check_error` alert.

## Direct Access Memory Map

The table below provides a detailed overview of the items stored in the OTP partitions.
Some of the items that are buffered in registers is readable via memory mapped CSRs, and these CSRs are linked in the table below.
Items that are not linked can only be accessed via the direct programming interface (if the partition is not locked via the corresponding digest).
It should be noted that CREATOR_SW_CFG and OWNER_SW_CFG are accessible through a memory mapped window, and content of these partitions is not buffered.
Hence, a read access to those windows will take in the order of 10-20 cycles until the read returns.

Sizes below are specified in multiples of 32bit words.

{{< snippet "hw/ip/otp_ctrl/doc/otp_ctrl_mmap.md" >}}

Note that since the content in the SECRET* partitions are scrambled using a 64bit PRESENT cipher, read and write access through the DAI needs to occur at a 64bit granularity.
Also, all digests (no matter whether they are SW or HW digests) have an access granule of 64bit.

The table below lists digests locations, and the corresponding locked partitions.

{{< snippet "hw/ip/otp_ctrl/doc/otp_ctrl_digests.md" >}}

Write access to the affected partition will be locked if the digest has a nonzero value.

For the software partition digests, it is entirely up to software to decide on the digest algorithm to be used.
Hardware will determine the lock condition only based on whether a non-zero value is present at that location or not.

For the hardware partitions, hardware calculates this digest and uses it for [background verification]({{< relref "#partition-checks" >}}).
Digest calculation can be triggered via the DAI.

Finally, it should be noted that the RMA_TOKEN and CREATOR_ROOT_KEY_SHARE0 / CREATOR_ROOT_KEY_SHARE1 items can only be programmed when the device is in the DEV, PROD, PROD_END and RMA stages.
Please consult the [life cycle controller documentation]({{< relref "hw/ip/lc_ctrl/doc" >}}) documentation for more information.

## Examples

### Provisioning Items

The following represents a typical provisioning sequence for items in all partitions (except for the LIFE_CYCLE partition, which is not software-programmable):

1. [Program]({{< relref "#programming-sequence" >}}) the item in 32bit or 64bit chunks via the DAI.
2. [Read back]({{< relref "#readout-sequence" >}}) and verify the item via the DAI.
3. If the item is exposed via CSRs or a CSR window, perform a full-system reset and verify whether those fields are correctly populated.

Note that any unrecoverable errors during the programming steps, or mismatches during the readback and verification steps indicate that the device might be malfunctioning (possibly due to fabrication defects) and hence the device may have to be scrapped.
This is however rare and should not happen after fabrication testing.

### Locking Partitions

Once a partition has been fully populated, write access to that partition has to be permanently locked.
For the HW_CFG and SECRET* partitions, this can be achieved as follows:

1. [Trigger]({{< relref "#digest-calculation-sequence" >}}) a digest calculation via the DAI.
2. [Read back]({{< relref "#readout-sequence" >}}) and verify the digest location via the DAI.
3. Perform a full-system reset and verify that the corresponding CSRs exposing the 64bit digest have been populated ({{< regref "HW_CFG_DIGEST_0" >}}, {{< regref "SECRET0_DIGEST_0" >}}, {{< regref "SECRET1_DIGEST_0" >}} or {{< regref "SECRET2_DIGEST_0" >}}).

It should be noted that locking only takes effect after a system reset since the affected partitions first have to re-sense the digest values.
Hence, it is critical that SW ensures that no more data is written to the partition to be locked after triggering the hardware digest calculation.
Otherwise, the device will likely be rendered inoperable as this can lead to permanent digest mismatch errors after system reboot.

For the {{< regref "CREATOR_SW_CFG" >}} and {{< regref "OWNER_SW_CFG" >}} partitions, the process is similar, but computation and programming of the digest is entirely up to software:

1. Compute a 64bit digest over the relevant parts of the partition, and [program]({{< relref "#programming-sequence" >}}) that value to {{< regref "CREATOR_SW_CFG_DIGEST_0" >}} or {{< regref "OWNER_SW_CFG_DIGEST_0" >}} via the DAI. Note that digest accesses through the DAI have an access granule of 64bit.
2. [Read back]({{< relref "#readout-sequence" >}}) and verify the digest location via the DAI.
3. Perform a full-system reset and verify that the corresponding digest CSRs {{< regref "CREATOR_SW_CFG_DIGEST_0" >}} or {{< regref "OWNER_SW_CFG_DIGEST_0" >}} have been populated with the correct 64bit value.

Note that any unrecoverable errors during the programming steps, or mismatches during the read-back and verification steps indicate that the device might be malfunctioning (possibly due to fabrication defects) and hence the device may have to be scrapped.
This is however rare and should not happen after fabrication testing.

## Register Table

{{< registers "hw/ip/otp_ctrl/data/otp_ctrl.hjson" >}}


# Additional Notes

## OTP IP Assumptions

It is assumed the OTP IP employed in production has reasonable physical defense characteristics.
Specifically which defensive features will likely be use case dependent, but at a minimum they should have the properties below.
Note some properties are worded with "SHALL" and others with "SHOULD".
"SHALL" refers to features that must be present, while "SHOULD" refers to features that are ideal, but optional.

- The contents shall not be observable via optical microscopy (for example anti-fuse technology).
- The IP lifetime shall not be limited by the amount of read cycles performed.
- If the IP contains field programmability (internal charge pumps and LDOs), there shall be mechanisms in place to selectively disable this function based on device context.
- If the IP contains redundant columns, rows, pages or banks for yield improvement, it shall provide a mechanism to lock down arbitrary manipulation of page / bank swapping during run-time.
- The IP shall be clear on what bits must be manipulated by the user, what bits are automatically manipulated by hardware (for example ECC or redundancy) and what areas the user can influence.
- The IP shall be compatible, through the use of a proprietary wrapper or shim, with an open-source friendly IO interface.
- The IP should functionally support the programming of already programmed bits without information leakage.
- The IP should offer SCA resistance:
  - For example, the content may be stored differentially.
  - For example, the sensing exhibits similar power signatures no matter if the stored bit is 0 or 1.
- The IP interface shall be memory-like if beyond a certain size.
- When a particular location is read, a fixed width output is returned; similar when a particular location is programmed, a fixed width input is supplied.
- The IP does not output all stored bits in parallel.
- The contents should be electrically hidden. For example, it should be difficult for an attacker to energize the fuse array and observe how the charge leaks.
- The IP should route critical nets at lower metal levels to avoid probing.
- The IP should contain native detectors for fault injection attacks.
- The IP should contain mechanisms to guard against interrupted programming - either through malicious intent or unexpected power loss and glitched address lines.
- The IP should contain mechanisms for error corrections (single bit errors).
- For example ECC or redundant bits voting / or-ing.
- As error correction mechanisms are technology dependent, that information should not be exposed to the open-source controller, instead the controller should simply receive information on whether a read / program was successful.
- The IP should have self-test functionality to assess the health of the storage and analog structures.
- The IP may contain native PUF-like functionality.

