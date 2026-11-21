# OTP Controller Technical Specification
<!-- BEGIN CMDGEN util/mdbook_regression_links.py --hjson hw/top_earlgrey/ip_autogen/otp_ctrl/data/otp_ctrl.hjson --top earlgrey -->
| Regression | Version | [Stages](https://opentitan.org/book/doc/project_governance/development_stages.html) | Results |
|-|-|-|-|
 [`otp_ctrl`](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/dashboard.html) | 3.0.0 | D2, V0 | ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/otp_ctrl/test.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/otp_ctrl/passing.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/otp_ctrl/functional.svg) ![](https://dashboard.reports.lowrisc.org/opentitan/earlgrey/badge/otp_ctrl/code.svg) |

This IP has been taped out in Earl Grey 1.0.0. The corresponding documentation and regression results can be found [here](https://opentitan.org/earlgrey_1.0.0/book/hw/ip/otp_ctrl/index.html).

<!-- END CMDGEN -->

# Overview

This document specifies the functionality of the one time programmable (OTP) memory controller.
The OTP controller is a module that is a peripheral on the chip interconnect bus, and thus follows the [Comportability Specification](../../../../doc/contributing/hw/comportability/README.md).

The OTP is a module that provides a device with one-time-programming functionality.
The result of this programming is non-volatile, and unlike flash, cannot be reversed.
The OTP functionality is constructed through an open-source OTP controller and a backend that provides the non-volatile storage.
The backend is either a dedicated, typically proprietary OTP IP wrapped in `otp_macro`, or `rram_ctrl`, which emulates OTP in a reserved region of the RRAM.
In this top, the backend is `rram_ctrl`.

The OTP controller provides:
- An open-source abstraction interface that software can use to interact with the OTP backend underneath.
- An open-source abstraction interface that hardware components (for example [life cycle controller](../../../ip/lc_ctrl/README.md) and [key manager](../../../ip/keymgr_dpe/README.md)) can use to interact with the OTP backend underneath.
- High level logical security protection, such as integrity checks and scrambling of sensitive content.
- Software isolation for when OTP contents are readable and programmable.

The backend provides:
- Reliable, non-volatile storage.
- Technology-specific redundancy or error correction mechanisms.
- Physical defensive features such as SCA and FI resistance.
- Visual and electrical probing resistance.

Together, the OTP controller and the backend provide secure one-time-programming functionality that is used throughout the life cycle (LC) of a device.
With the `rram_ctrl` backend, the OTP is emulated in a reserved region of the RRAM.
Since the RRAM itself is rewritable, the one-time-programmable behavior is enforced by `rram_ctrl`.
Writes from the OTP controller can only set bits, and software cannot read or program the OTP region through `rram_ctrl`.

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
- Lightweight key derivation function for the NVM (flash or RRAM) scrambling mechanism

## Supported Parameter Sets

The following table lists the instantiation parameters of OTP.
Note that parameters prefixed with `RndCnst` are random netlist constants that need to be regenerated via topgen before the tapeout (typically by the silicon creator).

Parameter                   | Default             | Top Earlgrey  | Description
----------------------------|---------------------|---------------|---------------
`AlertAsyncOn`              | `{NumAlerts{1'b1}}` | Set by topgen | Adds synchronizers to the alert senders for an alert handler on another clock.
`AlertSkewCycles`           | `1`                 | `1`           | Cycles of skew tolerated on the differential alert signals, set by topgen.
`RndCnstLfsrSeed`           | (see RTL)           | (see RTL)     | Seed to be used for the internal 40bit partition check timer LFSR. This needs to be replaced by the silicon creator before the tapeout.
`RndCnstLfsrPerm`           | (see RTL)           | (see RTL)     | Permutation to be used for the internal 40bit partition check timer LFSR. This needs to be replaced by the silicon creator before the tapeout.
`RndCnstScrmblKeyInit`      | (see RTL)           | (see RTL)     | Reset value of the scrambling key and nonce registers.
`RndCnstScrmblKey<i>`       | `'0`                | (see RTL)     | Random scrambling keys for secret partitions, to be used in the [scrambling datapath](doc/theory_of_operation.md#scrambling-datapath). There is one parameter per key in the memory map.
`RndCnstDigestConst<i>`     | `'0`                | (see RTL)     | Random digest finalization constants, to be used in the [scrambling datapath](doc/theory_of_operation.md#scrambling-datapath). There is one parameter per digest in the memory map.
`RndCnstDigestIV<i>`        | `'0`                | (see RTL)     | Random digest initialization vectors, to be used in the [scrambling datapath](doc/theory_of_operation.md#scrambling-datapath). There is one parameter per digest in the memory map.
`RndCnstPartInvDefault`     | `'0`                | (see RTL)     | Default value of the buffered partitions while they are invalid.

The OTP controller is generated by ipgen, and the following template parameters define its configuration.

Template Parameter          | Top Earlgrey | Description
----------------------------|------------------|---------------
`otp_mmap`                  | `hw/top_earlgrey/data/otp/otp_ctrl_mmap.hjson` | Memory map of the OTP partitions and items, and the scrambling configuration.
`enable_nvm_key`            | `true` | Enables the NVM scrambling key interface.
`num_sram_key_req_slots`    | `5` | Number of SRAM scrambling key request ports.

Only the configuration that this top generates, listed in the Top Earlgrey columns above, is verified and signed off.
The block-level testbench of this top is generated from the same memory map and template parameters, so it verifies the same configuration.
The random netlist constants do not change the architecture, so any value of them is supported.

## OTP Controller Overview

The functionality of OTP is split into the open-source OTP controller and a backend, with a clearly defined boundary in between, as illustrated in the simplified high-level block diagram below.

![OTP Controller Overview](./doc/otp_ctrl_overview.svg)

This top uses the `rram_ctrl` backend.

It is the task of the open-source controller to provide a common, non-technology specific interface to OTP users with a common register interface and a clearly defined I/O interface to hardware.
The open-source controller implements logical isolation and partitioning of OTP storage that enables users to separate different functions of the OTP into "partitions" with different properties.
Finally, the open-source controller provides a high level of security for specific partitions by provisioning integrity digests for each partition, and scrambling of partitions where required.

The backend on the other hand translates a common access interface, the macro interface, to the underlying storage.
Two backends are available.
- [`otp_macro`](../../../ip/otp_macro/README.md) wraps a dedicated, technology-specific OTP IP, both for functional and debug accesses (for example register accesses to the macro-internal control structure).
  In order to enable simulation and FPGA emulation of the OTP controller even without access to the proprietary OTP IP, `otp_macro` also contains a generalized and synthesizable model of the OTP IP.
- [`rram_ctrl`](../../../ip/rram_ctrl/README.md) emulates OTP in a reserved region of the RRAM.

This split implies that every backend must implement the standardized macro interface.
It also implies that no matter how the OTP storage or word size may change underneath, the open-source controller must present a consistent and coherent software and hardware interface.
The macro interface is described in the [theory of operation](doc/theory_of_operation.md#macro-interface-and-backends).
