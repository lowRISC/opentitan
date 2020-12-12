---
title: "OpenTitan Security"
---

## Overview

OpenTitan's mission is to create a trustworthy, vendor-agnostic open source
silicon Root of Trust (RoT) widely adopted across the industry. We do this by
implementing strong logical security integrity guarantees in the hardware and
firmware components, and restricting licensing of the OpenTitan trademark to
those implementations conforming to OpenTitan standards.

## [OpenTitan Security Model Specification][security_model]

The [OpenTitan Security Model Specification][security_model] defines the logical
security properties of the discrete IC. It covers device and software
attestation, provisioning, secure boot, chip lifecycle, firmware update, chip
identity, and chip ownership transfer.

## [Logical Security Model][logical_security_model]

The [OpenTitan Security Model][logical_security_model] provides a high level
framework for device provisioning and run-time operations. It starts by
enumerating the range of logical entities supported by the architecture, and
their mapping into software stages. Runtime isolation properties and baseline
identity concepts are introduced in this document.

## Functional Guarantees

At the functional level OpenTitan aims to provide the following guarantees:

*   Silicon Owners shall be able to deploy their own Root of Trust (RoT) Public
    Key Infrastructure (PKI) after taking ownership of the device.
*   Silicon Creators shall endorse the authenticity of the hardware. Endorsement
    is contingent on the silicon adhering to the physical implementation
    guidelines and standard requirements stipulated by the project. The
    endorsement shall be measurable via a Transport Certificate.
*   OpenTitan shall provide full boot attestation measurements to allow Silicon
    Owners to verify the boot chain configuration. The attestation chain shall
    be anchored in the Silicon Owner's RoT PKI.
*   OpenTitan shall provide a key manager implementation strongly bound to the
    boot chain. Only a boot chain signed with the expected set of keys shall be
    able to unlock stored keys/secrets.
*   OpenTitan shall provide a key versioning scheme with support for key
    migration bound to the firmware versioning and update implementation.

## Use Cases

The security goals of the project are derived from a list of target use cases.
See [OpenTitan's Use Cases][use_cases] for more details. The security goals are
used to define OpenTitan's threat model, as well as functional and assurance
security requirements. Such requirements influence the system architecture, as
well as the certification strategy for silicon implementations.

## Security Primitives

All hardware security primitives adhere to the OpenTitan
[comportable][comportable_ip] peripheral interface specification.
Implementations for some of these components are available for reference and
may not meet production or certification criteria yet.

### [Entropy source][entropy_source]

Digital wrapper for a NIST SP 800-90B compliant entropy source. An additional
emulated entropy source implementation will be available for FPGA functional
testing.

### [CSRNG][csrng]

Cryptographically Secure Random Number Generator (CSRNG) providing support for
both deterministic (DRBG) and true random number generation (TRNG).

The DRBG is implemented using the `CTR_DRBG` construction specified in
NIST SP 800-90A.

### [AES][aes]

Advanced Encryption Standard (AES) supporting Encryption/Decryption using
128/192/256 bit key sizes in the following cipher block modes:

*   Electronic Codebook (ECB) mode,
*   Cipher Block Chaining (CBC) mode,
*   Cipher Feedback (CFB) mode with fixed data segment size of 128 bits,
*   Output Feedback (OFB) mode, and
*   Counter (CTR) mode.

### [HMAC][hmac]

HMAC with SHA-2 FIPS 180-4 compliant hash function, supporting both
HMAC-SHA256 and SHA256 modes of operation.

### [Key Manager][keymgr]

Hardware backed symmetric key generation and storage providing key isolation
from software.

### [OTBN][otbn]

Public key algorithm accelerator with support for bignum operations in hardware.

### [Alert Handler][alert_handler]

Aggregates alert signals from other system components designated as potential
security threats, converting them to processor interrupts. It also supports
alert policy assignments to handle alerts completely in hardware depending on
the assigned severity.

[aes]: {{< relref "hw/ip/aes/doc" >}}
[alert_handler]: {{< relref "hw/ip/alert_handler/doc" >}}
[comportable_ip]: {{< relref "doc/rm/comportability_specification" >}}
[csrng]: {{< relref "hw/ip/csrng/doc" >}}
[entropy_source]: {{< relref "hw/ip/entropy_src/doc" >}}
[hmac]: {{< relref "hw/ip/hmac/doc" >}}
[keymgr]: {{< relref "hw/ip/keymgr/doc" >}}
[logical_security_model]: {{< relref "doc/security/logical_security_model" >}}
[otbn]: {{< relref "hw/ip/otbn/doc" >}}
[security_model]: {{< relref "doc/security/specs" >}}
[use_cases]: {{< relref "doc/security/use_cases" >}}
