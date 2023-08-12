# Programmer's Guide

During provisioning and manufacturing, SW interacts with the OTP controller mostly through the Direct Access Interface (DAI), which is described below.
Afterwards during production, SW is expected to perform only read accesses via the exposed CSRs and CSR windows, since all write access to the partitions has been locked down.

The following sections provide some general guidance, followed by an explanation of the DAI and a detailed OTP memory map.
Typical programming sequences are explained at the end of the Programmer's guide.

## General Guidance

### Initialization

The OTP controller initializes automatically upon power-up and is fully operational by the time the processor boots.
The only initialization steps that SW should perform are:

1. Check that the OTP controller has successfully initialized by reading [`STATUS`](registers.md#status). I.e., make sure that none of the ERROR bits are set, and that the DAI is idle ([`STATUS.DAI_IDLE`](registers.md#status)).
2. Set up the periodic background checks:
    - Choose whether to enable periodic [background checks](#partition-checks) by programming nonzero mask values to [`INTEGRITY_CHECK_PERIOD`](registers.md#integrity_check_period) and [`CONSISTENCY_CHECK_PERIOD`](registers.md#consistency_check_period).
    - Choose whether such checks shall be subject to a timeout by programming a nonzero timeout cycle count to [`CHECK_TIMEOUT`](registers.md#check_timeout).
    - It is recommended to lock down the background check registers via [`CHECK_REGWEN`](registers.md#check_regwen), once the background checks have been set up.

If needed, one-off integrity and consistency checks can be triggered via [`CHECK_TRIGGER`](registers.md#check_trigger).
If this functionality is not needed, it is recommended to lock down the trigger register via [`CHECK_TRIGGER_REGWEN`](registers.md#check_trigger_regwen).

Later on during the boot process, SW may also choose to block read access to the CREATOR_SW_CFG or OWNER_SW_CFG partitions at runtime via [`CREATOR_SW_CFG_READ_LOCK`](registers.md#creator_sw_cfg_read_lock) and [`OWNER_SW_CFG_READ_LOCK`](registers.md#owner_sw_cfg_read_lock).


### Reset Considerations

It is important to note that values in OTP **can be corrupted** if a reset occurs during a programming operation.
This should be of minor concern for SW, however, since all partitions except for the LIFE_CYCLE partition are being provisioned in secure and controlled environments, and not in the field.
The LIFE_CYCLE partition is the only partition that is modified in the field - but that partition is entirely owned by the life cycle controller and not by SW.

### Programming Already Programmed Regions

OTP words cannot be programmed twice, and doing so may damage the memory array.
Hence the OTP controller performs a blank check and returns an error if a write operation is issued to an already programmed location.

### Potential Side-Effects on Flash via Life Cycle

It should be noted that the locked status of the partition holding the creator root key (i.e., the value of the [`SECRET2_DIGEST_0`](registers.md#secret2_digest)) determines the ID_STATUS of the device, which in turn determines SW accessibility of creator seed material in flash and OTP.
That means that creator-seed-related collateral needs to be provisioned to Flash **before** the OTP digest lockdown mechanism is triggered, since otherwise accessibility to the corresponding flash region is lost.
See the [life cycle controller documentation](../../lc_ctrl/README.md#id-state-of-the-device) for more details.

## Direct Access Interface

OTP has to be programmed via the Direct Access Interface, which is comprised of the following CSRs:

CSR Name                             | Description
-------------------------------------|------------------------------------
[`DIRECT_ACCESS_WDATA_0`](registers.md#direct_access_wdata) | Low 32bit word to be written.
[`DIRECT_ACCESS_WDATA_1`](registers.md#direct_access_wdata) | High 32bit word to be written.
[`DIRECT_ACCESS_RDATA_0`](registers.md#direct_access_rdata) | Low 32bit word that has been read.
[`DIRECT_ACCESS_RDATA_1`](registers.md#direct_access_rdata) | High 32bit word that has been read.
[`DIRECT_ACCESS_ADDRESS`](registers.md#direct_access_address) | byte address for the access.
[`DIRECT_ACCESS_CMD`](registers.md#direct_access_cmd)     | Command register to trigger a read or a write access.
[`DIRECT_ACCESS_REGWEN`](registers.md#direct_access_regwen)  | Write protection register for DAI.

See further below for a detailed [Memory Map](#direct-access-memory-map) of the address space accessible via the DAI.

### Readout Sequence

A typical readout sequence looks as follows:

1. Check whether the DAI is idle by reading the [`STATUS`](registers.md#status) register.
2. Write the byte address for the access to [`DIRECT_ACCESS_ADDRESS`](registers.md#direct_access_address).
Note that the address is aligned with the granule, meaning that either 2 or 3 LSBs of the address are ignored, depending on whether the access granule is 32 or 64bit.
3. Trigger a read command by writing 0x1 to [`DIRECT_ACCESS_CMD`](registers.md#direct_access_cmd).
4. Poll the [`STATUS`](registers.md#status) until the DAI state goes back to idle.
Alternatively, the `otp_operation_done` interrupt can be enabled up to notify the processor once an access has completed.
5. If the status register flags a DAI error, additional handling is required (see [Section on Error handling](#error-handling)).
6. If the region accessed has a 32bit access granule, the 32bit chunk of read data can be read from [`DIRECT_ACCESS_RDATA_0`](registers.md#direct_access_rdata).
If the region accessed has a 64bit access granule, the 64bit chunk of read data can be read from the [`DIRECT_ACCESS_RDATA_0`](registers.md#direct_access_rdata) and [`DIRECT_ACCESS_RDATA_1`](registers.md#direct_access_rdata) registers.
7. Go back to 1. and repeat until all data has been read.

The hardware will set [`DIRECT_ACCESS_REGWEN`](registers.md#direct_access_regwen) to 0x0 while an operation is pending in order to temporarily lock write access to the CSRs registers.

### Programming Sequence

A typical programming sequence looks as follows:

1. Check whether the DAI is idle by reading the [`STATUS`](registers.md#status) register.
2. If the region to be accessed has a 32bit access granule, place a 32bit chunk of data into [`DIRECT_ACCESS_WDATA_0`](registers.md#direct_access_wdata).
If the region to be accessed has a 64bit access granule, both the [`DIRECT_ACCESS_WDATA_0`](registers.md#direct_access_wdata) and [`DIRECT_ACCESS_WDATA_1`](registers.md#direct_access_wdata) registers have to be used.
3. Write the byte address for the access to [`DIRECT_ACCESS_ADDRESS`](registers.md#direct_access_address).
Note that the address is aligned with the granule, meaning that either 2 or 3 LSBs of the address are ignored, depending on whether the access granule is 32 or 64bit.
4. Trigger a write command by writing 0x2 to [`DIRECT_ACCESS_CMD`](registers.md#direct_access_cmd).
5. Poll the [`STATUS`](registers.md#status) until the DAI state goes back to idle.
Alternatively, the `otp_operation_done` interrupt can be enabled up to notify the processor once an access has completed.
6. If the status register flags a DAI error, additional handling is required (see [Section on Error handling](#error-handling)).
7. Go back to 1. and repeat until all data has been written.

The hardware will set [`DIRECT_ACCESS_REGWEN`](registers.md#direct_access_regwen) to 0x0 while an operation is pending in order to temporarily lock write access to the CSRs registers.

Note that SW is responsible for keeping track of already programmed OTP word locations during the provisioning phase.
**It is imperative that SW does not write the same word location twice**, since this can lead to ECC inconsistencies, thereby potentially rendering the device useless.

### Digest Calculation Sequence

The hardware digest computation for the hardware and secret partitions can be triggered as follows:

1. Check whether the DAI is idle by reading the [`STATUS`](registers.md#status) register.
3. Write the partition base address to [`DIRECT_ACCESS_ADDRESS`](registers.md#direct_access_address).
4. Trigger a digest calculation command by writing 0x4 to [`DIRECT_ACCESS_CMD`](registers.md#direct_access_cmd).
5. Poll the [`STATUS`](registers.md#status) until the DAI state goes back to idle.
Alternatively, the `otp_operation_done` interrupt can be enabled up to notify the processor once an access has completed.
6. If the status register flags a DAI error, additional handling is required (see [Section on Error handling](#error-handling)).

The hardware will set [`DIRECT_ACCESS_REGWEN`](registers.md#direct_access_regwen) to 0x0 while an operation is pending in order to temporarily lock write access to the CSRs registers.

It should also be noted that the effect of locking a partition via the digest only takes effect **after** the next system reset.
To prevent integrity check failures SW must therefore ensure that no more programming operations are issued to the affected partition after initiating the digest calculation sequence.

### Software Integrity Handling

As opposed to buffered partitions, the digest and integrity handling of unbuffered partitions is entirely up to software.
The only hardware-assisted feature in unbuffered partitions is the digest lock, which locks write access to an unbuffered partition once a nonzero value has been programmed to the 64bit digest location.

In a similar vein, it should be noted that the system-wide bus-integrity metadata does not travel alongside the data end-to-end in the OTP controller (i.e., the  bus-integrity metadata bits are not stored into the OTP memory array).
This means that data written to and read from the OTP macro is not protected by the bus integrity feature at all stages.
In case of buffered partitions this does not pose a concern since data integrity in these partitions is checked via the hardware assisted digest mechanism.
In case of unbuffered partitions however, the data integrity checking is entirely up to software.
I.e., if data is read from an unbuffered partition (either through the DAI or CSR windows), software should perform an integrity check on that data.

## Error Handling

The agents that can access the OTP macro (DAI, LCI, buffered/unbuffered partitions) expose detailed error codes that can be used to root cause any failure.
The error codes are defined in the table below, and the corresponding `otp_err_e` enum type can be found in the `otp_ctrl_pkg`.
The table also lists which error codes are supported by which agent.

Errors that are not "recoverable" are severe errors that move the corresponding partition or DAI/LCI FSM into a terminal error state, where no more commands can be accepted (a system reset is required to restore functionality in that case).
Errors that are "recoverable" are less severe and do not cause the FSM to jump into a terminal error state.

Note that error codes that originate in the physical OTP macro are prefixed with `Macro*`.

Error Code | Enum Name              | Recoverable | DAI | LCI | Unbuf | Buf   | Description
-----------|------------------------|-------------|-----|-----|-------|-------|-------------
0x0        | `NoError`              | -           |  x  |  x  |   x   |  x    | No error has occurred.
0x1        | `MacroError`           | no          |  x  |  x  |   x   |  x    | Returned if the OTP macro command did not complete successfully due to a macro malfunction.
0x2        | `MacroEccCorrError`    | yes         |  x  |  -  |   x   |  x    | A correctable ECC error has occurred during a read operation in the OTP macro.
0x3        | `MacroEccUncorrError`  | no          |  x  |  -  |   x*  |  x    | An uncorrectable ECC error has occurred during a read operation in the OTP macro. Note (*): This error is collapsed into `MacroEccCorrError` if the partition is a vendor test partition. It then becomes a recoverable error.
0x4        | `MacroWriteBlankError` | yes / no*   |  x  |  x  |   -   |  -    | This error is returned if a write operation attempted to clear an already programmed bit location. Note (*): This error is recoverable if encountered in the DAI, but unrecoverable if encountered in the LCI.
0x5        | `AccessError`          | yes         |  x  |  -  |   x   |  -    | An access error has occurred (e.g. write to write-locked region, or read to a read-locked region).
0x6        | `CheckFailError`       | no          |  -  |  -  |   x   |  x    | An unrecoverable ECC, integrity or consistency error has been detected.
0x7        | `FsmStateError`        | no          |  x  |  x  |   x   |  x    | The FSM has been glitched into an invalid state, or escalation has been triggered and the FSM has been moved into a terminal error state.

All non-zero error codes listed above trigger an `otp_error` interrupt.
In addition, all unrecoverable OTP `Macro*` errors (codes 0x1, 0x3) trigger a `fatal_macro_error` alert, while all remaining unrecoverable errors trigger a `fatal_check_error` alert.

If software receives an `otp_error` interrupt, but all error codes read back as 0x0 (`NoError`), this should be treated as a fatal error condition, and the system should be shut down as soon as possible.

Note that while the `MacroWriteBlankError` is marked as a recoverable error, the affected OTP word may be in an inconsistent state after this error has been returned.
This can cause several issues when the word is accessed again (either as part of a regular read operation, as part of the readout at boot, or as part of a background check).
It is important that SW ensures that each word is only written once, since this can render the device useless.

## Direct Access Memory Map

The table below provides a detailed overview of the items stored in the OTP partitions.
Some of the items that are buffered in registers is readable via memory mapped CSRs, and these CSRs are linked in the table below.
Items that are not linked can only be accessed via the direct programming interface (if the partition is not locked via the corresponding digest).
It should be noted that CREATOR_SW_CFG and OWNER_SW_CFG are accessible through a memory mapped window, and content of these partitions is not buffered.
Hence, a read access to those windows will take in the order of 10-20 cycles until the read returns.

Sizes below are specified in multiples of 32bit words.

{{#include otp_ctrl_mmap.md}}

Note that since the content in the SECRET* partitions are scrambled using a 64bit PRESENT cipher, read and write access through the DAI needs to occur at a 64bit granularity.
Also, all digests (no matter whether they are SW or HW digests) have an access granule of 64bit.

The table below lists digests locations, and the corresponding locked partitions.

{{#include otp_ctrl_digests.md}}

Write access to the affected partition will be locked if the digest has a nonzero value.

For the software partition digests, it is entirely up to software to decide on the digest algorithm to be used.
Hardware will determine the lock condition only based on whether a non-zero value is present at that location or not.

For the hardware partitions, hardware calculates this digest and uses it for [background verification](#partition-checks).
Digest calculation can be triggered via the DAI.

Finally, it should be noted that the RMA_TOKEN and CREATOR_ROOT_KEY_SHARE0 / CREATOR_ROOT_KEY_SHARE1 items can only be programmed when the device is in the DEV, PROD, PROD_END and RMA stages.
Please consult the [life cycle controller documentation](../../lc_ctrl/README.md) documentation for more information.

## Examples

### Provisioning Items

The following represents a typical provisioning sequence for items in all partitions (except for the LIFE_CYCLE partition, which is not software-programmable):

1. [Program](#programming-sequence) the item in 32bit or 64bit chunks via the DAI.
2. [Read back](#readout-sequence) and verify the item via the DAI.
3. If the item is exposed via CSRs or a CSR window, perform a full-system reset and verify whether those fields are correctly populated.

Note that any unrecoverable errors during the programming steps, or mismatches during the readback and verification steps indicate that the device might be malfunctioning (possibly due to fabrication defects) and hence the device may have to be scrapped.
This is however rare and should not happen after fabrication testing.

### Locking Partitions

Once a partition has been fully populated, write access to that partition has to be permanently locked.
For the HW_CFG and SECRET* partitions, this can be achieved as follows:

1. [Trigger](#digest-calculation-sequence) a digest calculation via the DAI.
2. [Read back](#readout-sequence) and verify the digest location via the DAI.
3. Perform a full-system reset and verify that the corresponding CSRs exposing the 64bit digest have been populated ([`HW_CFG_DIGEST_0`](registers.md#hw_cfg_digest), [`SECRET0_DIGEST_0`](registers.md#secret0_digest), [`SECRET1_DIGEST_0`](registers.md#secret1_digest) or [`SECRET2_DIGEST_0`](registers.md#secret2_digest)).

It should be noted that locking only takes effect after a system reset since the affected partitions first have to re-sense the digest values.
Hence, it is critical that SW ensures that no more data is written to the partition to be locked after triggering the hardware digest calculation.
Otherwise, the device will likely be rendered inoperable as this can lead to permanent digest mismatch errors after system reboot.

For the [`CREATOR_SW_CFG`](registers.md#creator_sw_cfg) and [`OWNER_SW_CFG`](registers.md#owner_sw_cfg) partitions, the process is similar, but computation and programming of the digest is entirely up to software:

1. Compute a 64bit digest over the relevant parts of the partition, and [program](#programming-sequence) that value to [`CREATOR_SW_CFG_DIGEST_0`](registers.md#creator_sw_cfg_digest) or [`OWNER_SW_CFG_DIGEST_0`](registers.md#owner_sw_cfg_digest) via the DAI. Note that digest accesses through the DAI have an access granule of 64bit.
2. [Read back](#readout-sequence) and verify the digest location via the DAI.
3. Perform a full-system reset and verify that the corresponding digest CSRs [`CREATOR_SW_CFG_DIGEST_0`](registers.md#creator_sw_cfg_digest) or [`OWNER_SW_CFG_DIGEST_0`](registers.md#owner_sw_cfg_digest) have been populated with the correct 64bit value.

Note that any unrecoverable errors during the programming steps, or mismatches during the read-back and verification steps indicate that the device might be malfunctioning (possibly due to fabrication defects) and hence the device may have to be scrapped.
This is however rare and should not happen after fabrication testing.

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_otp_ctrl.h)

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
