# Implementation Status

This document lists where the RTL of the I3C IP block does not implement the capabilities that the specification documents describe yet.
It also links the issues that track the incomplete features, bugs and deviations from the I3C specifications.
Features that the specification documents list as unsupported or undecided are not listed here.

For the integration of the IP block in Earl Grey, see the [I3C section of the Earl Grey chip specification](../../../top_earlgrey/doc/design/README.md#i3c).

## Controller

### HCI and TCRI features

The following [HCI and TCRI features](theory_of_operation.md#supported-hci-and-tcri-features) are not implemented or only partially implemented:

| Feature                                                        | Status          | Notes                                                                                                                                                                                          | Issue                                                       |
|----------------------------------------------------------------|-----------------|------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|-------------------------------------------------------------|
| Address Assignment Command (ENTDAA, SETDASA)                   | Partial         | The ENTDAA sequence is incomplete.                                                                                                                                                             | [#31304](https://github.com/lowRISC/opentitan/issues/31304) |
| Internal Control Commands                                      | Partial         | Broadcast Address Enable; Target Reset Pattern only without RSTACT; Controller SDA Recovery is rejected with `NOT_SUPPORTED`.                                                                  | [#31304](https://github.com/lowRISC/opentitan/issues/31304) |
| In-Band Interrupts                                             | Partial         | No DISEC is issued after an IBI is rejected.                                                                                                                                                   | [#31304](https://github.com/lowRISC/opentitan/issues/31304) |
| ENDXFER negotiation in HDR-DDR mode                            | Not implemented | The Internal Control Command is accepted without effect.                                                                                                                                       | [#31304](https://github.com/lowRISC/opentitan/issues/31304) |
| Periodic bus traffic for passive Hot-Join and IBI Targets      | Not implemented |                                                                                                                                                                                                | [#31304](https://github.com/lowRISC/opentitan/issues/31304) |
| Abort, suspend and resume of command processing; halt on error | Partial         | `PIO_CONTROL.ABORT` stops the dispatch of commands, but `HC_CONTROL.ABORT` does not; the Controller never suspends on an error, see [Controller error reporting](#controller-error-reporting). | [#31304](https://github.com/lowRISC/opentitan/issues/31304) |
| Error detection and reporting                                  | Partial         | See [Controller error reporting](#controller-error-reporting).                                                                                                                                 | [#31305](https://github.com/lowRISC/opentitan/issues/31305) |
| Debug Specific Extended Capability (0x0C)                      | Partial         |                                                                                                                                                                                                | [#31307](https://github.com/lowRISC/opentitan/issues/31307) |

### Other Controller features

- [Address blocking](theory_of_operation.md#address-blocking): [`BLOCKED_ADDR`](registers.md#blocked_addr) is present but not enforced ([#31307](https://github.com/lowRISC/opentitan/issues/31307)).

### Controller error reporting

The [error detection and reporting](theory_of_operation.md#error-detection-and-reporting) of the Controller is incomplete ([#31304](https://github.com/lowRISC/opentitan/issues/31304), [#31305](https://github.com/lowRISC/opentitan/issues/31305)):

- The Controller reports only the error status codes `SUCCESS`, `CRC`, `PARITY`, `NACK` and `NOT_SUPPORTED`.
- The Controller does not detect the Controller Error Types CE0 and CE1.
- The Controller does not raise the transfer error interrupt and does not halt command processing on an error.

## Target

### CCCs

The following [CCCs](tti.md#supported-cccs) are not implemented or only partially implemented:

| CCC                                        | Status          | Notes                                                                                                                                            | Issue                                                                                                                      |
|--------------------------------------------|-----------------|--------------------------------------------------------------------------------------------------------------------------------------------------|----------------------------------------------------------------------------------------------------------------------------|
| ENTAS0-3 (Direct)                          | Not implemented | The Target does not acknowledge the Direct forms.                                                                                                | [#31128](https://github.com/lowRISC/opentitan/issues/31128)                                                                |
| ENTDAA                                     | Not implemented |                                                                                                                                                  | [#31128](https://github.com/lowRISC/opentitan/issues/31128)                                                                |
| ENDXFER                                    | Partial         | The HDR-DDR transfer-ending options are incomplete.                                                                                              | [#31065](https://github.com/lowRISC/opentitan/issues/31065)                                                                |
| RSTACT                                     | Partial         | The Target records the reset action; the GET form and most actions are incomplete.                                                              | [#31128](https://github.com/lowRISC/opentitan/issues/31128), [#31337](https://github.com/lowRISC/opentitan/issues/31337) |
| SETDASA                                    | Partial         |                                                                                                                                                  | [#31128](https://github.com/lowRISC/opentitan/issues/31128)                                                                |
| GETSTATUS                                  | Partial         | The pending interrupt field reads as zero.                                                                                                       | [#31128](https://github.com/lowRISC/opentitan/issues/31128)                                                                |
| GETACCCR                                   | Deviation       | The Target acknowledges GETACCCR, although it cannot assume the Controller role.                                                                 | [#31128](https://github.com/lowRISC/opentitan/issues/31128)                                                                |
| GETCAPS                                    | Partial         | `GETCAP1` always declares HDR-DDR support; `GETCAP2` and `GETCAP3` declare HDR-DDR Abort CRC, Write Abort and Pending Read Notification support. | [#31065](https://github.com/lowRISC/opentitan/issues/31065), [#31337](https://github.com/lowRISC/opentitan/issues/31337) |
| Direct SET CCCs to a Group Address         | Partial         | The Virtual Targets do not respect their group membership.                                                                                       | [#31128](https://github.com/lowRISC/opentitan/issues/31128)                                                                |
| Broadcast and multi-target Direct SET CCCs | Partial         | They take no effect when terminated by a Repeated START.                                                                                         | [#31128](https://github.com/lowRISC/opentitan/issues/31128)                                                                |

### Asynchronous Event Queue

The layouts of two [Asynchronous Event Descriptors](tti.md#asynchronous-event-types) differ from the TTI specification ([#31337](https://github.com/lowRISC/opentitan/issues/31337)):

- Type 0 (CCC activity): the `Has Data` bit is missing, and `Has DEFB` is at bit 17 instead of bit 18.
- Type 5 (bus events): the events are at bits 27:20 instead of bits 23:16.

### Other Target features

- [Hot-Join](tti.md#hot-join-feature): the Target does not act on `TARG_CONTROL.HJ_REQUEST` ([#31337](https://github.com/lowRISC/opentitan/issues/31337)).
- [HDR Restart Pattern](theory_of_operation.md#hdr-exit-and-hdr-restart-detection): the Target does not act on it ([#31035](https://github.com/lowRISC/opentitan/issues/31035)).
- [Disabling HDR-DDR mode](tti.md#target-support-for-hdr-ddr-signaling): the field `TARG_CONTROL.EN_HDR_DDR` is not in the register map, so the Target always declares support for HDR-DDR mode in its GETCAPS response ([#31337](https://github.com/lowRISC/opentitan/issues/31337)).

## Primary partition

- [Separated Enables output driver style](integration_notes.md#separated-enables-rtlio_sepi3c_io_pkgsv): the primary partition does not map its signals onto the CIO pins, so this style cannot be used ([#31762](https://github.com/lowRISC/opentitan/issues/31762)).
- [Virtual Open Drain output driver style](integration_notes.md#virtual-open-drain-rtlio_vodi3c_io_pkgsv): the logic between the last flip-flops and `cio_sda_en_o` has not been checked yet for glitches, which could appear as START or STOP conditions while SCL is high ([#31762](https://github.com/lowRISC/opentitan/issues/31762)).
- [`ctrl_scl_pu_en_o`](integration_notes.md#pullups-and-high-keepers) is always deasserted.

## Target Reset Detector

The [Target Reset Detector](integration_notes.md#target-reset-detector) in the secondary partition is incomplete:

- The primary partition does not maintain the detector enable and configuration while it is in a sleep state, and the activation and deactivation of the detector with the slow AON clock have not been checked yet ([#31337](https://github.com/lowRISC/opentitan/issues/31337)).
- The secondary partition ties the scan inputs of the detector off, so its flip-flops are not scanned ([#31335](https://github.com/lowRISC/opentitan/issues/31335)).
