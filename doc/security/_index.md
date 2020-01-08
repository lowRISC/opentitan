---
title: "OpenTitan Security Overview"
---

## Overview

OpenTitan's mission is to create a trustworthy, vendor-agnostic open source silicon Root of Trust (RoT) widely adopted across the industry.
We do this by implementing strong logical security integrity guarantees in the hardware and firmware components, and restricting licensing of the OpenTitan trademark to those implementations conforming to OpenTitan standards.

## Logical Security Model

The [OpenTitan Security Model][2] provides a high level framework for device provisioning and run-time operations.
It starts by enumerating the range of logical entities supported by the architecture, and their mapping into software stages.
Runtime isolation properties and baseline identity concepts are introduced in this document.

## Functional Guarantees

At the functional level OpenTitan aims to provide the following guarantees:

* Silicon Owners shall be able to deploy their own Root of Trust (RoT) Public Key Infrastructure (PKI) after taking ownership of the device.
* Silicon Creators shall endorse the authenticity of the hardware.
  Endorsement is contingent on the silicon adhering to the physical implementation guidelines and standard requirements stipulated by the project.
  The endorsement shall be measurable via a Transport Certificate.
* OpenTitan shall provide full boot attestation measurements to allow Silicon Owners to verify the boot chain configuration.
  The attestation chain shall be anchored in the Silicon Owner's RoT PKI.
* OpenTitan shall provide a key manager implementation strongly bound to the boot chain.
  Only a boot chain signed with the expected set of keys shall be able to unlock stored keys/secrets.
* OpenTitan shall provide a key versioning scheme with support for key migration bound to the firmware versioning and update implementation.

## Use Cases

The security goals of the project are derived from a list of target use cases.
See [OpenTitan's Use Cases][1] for more details.
The security goals are used to define OpenTitan's threat model, as well as functional and assurance security requirements.
Such requirements influence the system architecture, as well as the certification strategy for silicon implementations.

## Security Primitives

All hardware security primitives adhere to the OpenTitan [comportable][3] peripheral interface specification.
Implementations for some of these components are available for reference and may not meet production or certification criteria yet.

| Block Name | Description |
| ---------- | ----------- |
| TRNG Digital Wrapper | Digital wrapper for a NIST SP 800-90 compliant entropy source. <br> An additional emulated entropy source implementation will be available for FPGA functional testing. |
| DRBG | Proposed: DRBG-HMAC-SHA-2* NIST 800-90A.rev1 compliant. |
| [AES][8] | AES ECB/CBC/CTR 128/192/256 NIST 800-38A compliant. |
| [HMAC-SHA-2][9] | HMAC_SHA-2 NIST FIPS 180-4 compliant supporting both HMAC and SHA modes of operation. |
| Key Manager | Proposed: Hardware backed symmetric key generation and storage providing strong isolation properties. |
| Crypto Co-Processor | Proposed: Public key cryptography accelerator with support for bignum operations in hardware. |
| [Alert Handler][10] | Aggregates alert signals from other system components designated as potential security threats, converting them to processor interrupts. It also supports alert policy assignments to handle alerts completely in hardware. |


## Features

### Device Life Cycle

OpenTitan supports a set of operational states configured via One Time Programmable (OTP) memory, allowing the [Silicon Creator][4] to manage the state of the device as it is being manufactured and provisioned for shipment.

An additional set of life cycle states are also available to encapsulate the device ownership state.
A device that has been personalized with a unique [Creator Identity][4] can be provisioned with [Silicon Owner][5] credentials.
This enables the [Silicon Owner][5] to run signed code on the device.

### Secure Boot

OpenTitan supports a secure boot implementation anchored in the silicon mask ROM.
The mask ROM contains a set of public keys used to verify the first boot stage stored in flash.
Isolation between boot stages is enforced by a one way execution model where the current software stage is not allowed to call code in previous stages.

Each boot stage is in charge of verifying the signature of the next stage and locking out portions of the chip that are not required by later stages.
Once the boot flow reaches kernel execution, the implementation may opt to implement dynamic isolation between applications using the available [Physical Memory Protection][6] (PMP) unit.

### A/B Firmware Updates

OpenTitan supports a firmware layout with two flash partitions, supporting active and non-active instances of each software component.
This enables a firmware update implementation in which the active partition flashes the new software into the non-active region with minimal downtime.
Secure boot ensures the integrity and stability of the new software before marking it as active.

Each boot stage is expected to try to launch the newest available version of the next boot stage upon successful signature verification.
Newest is defined as the software with a more recent build timestamp or larger versioning value.

### Strong Cryptographic Identity

Each OpenTitan silicon device is personalized as part of the manufacturing process with entropy, a unique global identifier, and other values, which are the basis of the chip's cryptographic identity.
This identity is referred to as the Creator Identity, and it is fixed throughout the lifetime of the silicon.

The Creator Identity is endorsed via a Transport Creator Certificate which can be used in device authenticity attestation flows.

The Creator Identity is a component of other derived identities that are generated with additional input parameters from the software running on the device, as well as other components provisioned by the Silicon Owner.

### Ownership Transfer

The owner of the silicon is allowed to change in a process known as Ownership Transfer.
During this process, the existing owner shall wipe any stored secrets before relinquishing ownership of the device.
At this point a new party can take ownership of the device and provision its own identity.
This allows the new Silicon Owner to run its own signed code with attestation measurements anchored in the PKI of their choice.
Attested software can then proceed to provision entropy into the key manager plus additional constants to generate hidden keys strongly bound to the software configuration.

More details for this are available in the [OpenTitan Security Model][7].


[1]: {{< relref "doc/security/use_cases" >}}
[2]: {{< relref "doc/security/logical_security_model" >}}
[3]: {{< relref "doc/rm/comportability_specification" >}}
[4]: {{< relref "doc/security/logical_security_model#silicon-creator" >}}
[5]: {{< relref "doc/security/logical_security_model#silicon-owner" >}}
[6]: https://ibex-core.readthedocs.io/en/latest/pmp.html
[7]: {{< relref "doc/security/logical_security_model#owner-assignment" >}}
[8]: {{< relref "hw/ip/aes/doc" >}}
[9]: {{< relref "hw/ip/hmac/doc" >}}
[10]: {{< relref "hw/ip/alert_handler/doc" >}}
