---
title: "Trusted Platform Module - TPM"
---

## Overview

OpenTitan can be used to implement the full Trusted Platform Module (TPM) 2.0
specification to meet client and server platform use cases. When used as a TPM,
OpenTitan is provisioned with an endorsement seed and RSA and ECDSA endorsement
certificates (EK). TPM commands are served over either SPI or I2C device
peripherals.

## Certification Requirements

*   [ANSSI-CC-PP-2018/03](https://trustedcomputinggroup.org/wp-content/uploads/TCG_PCClient_PP_1p3_for_Library_1p59_pub_29sept2021.pdf)
    Protection Profile Client Specific TPM[^1]. The minimum assurance level for
    this Protection Profile (PP) is EAL 4 augmented with ALC\_FLR.1 and
    AVA\_VAN.4.

    *   ALC\_FLR.1: Basic flaw remediation. The developer provides flaw
        remediation procedures to the Target of Evaluation (TOE) developers.
    *   AVA\_VAN.4: Methodical vulnerability analysis. Methodical vulnerability
        analysis is performed by the evaluator to identify the presence of
        potential vulnerabilities. Penetration testing is performed by the
        evaluator with a _moderate _attack potential.

## Minimum Crypto Algorithm Requirements

*   TRNG: At least one internal entropy source is required. The entropy source
    and collector should provide entropy to the state register in a manner that
    is not visible to an outside process. The entropy collector should regularly
    update the state register with additional, unbiased entropy.
*   Hash Algorithms:
    *   An approved hash algorithm with approximately the same security strength
        as its strongest asymmetric algorithm. For OpenTitan the target is
        SHA2-256 (hardware), SHA3-384 (software implementation).
    *   A TPM should support the extend function to make incremental updates to
        a digest value.
*   Symmetric Key Algorithms:
    *   HMAC as described in ISO/IEC 9797-2. XOR obfuscation for use in a hash
        based stream cipher.
    *   A symmetric block cipher in CFB mode. For OpenTitan the target is
        AES-CFB 128/192/256-bit.
*   Asymmetric key algorithm:
    *   At least one of:
        *   RSA:
            *   Sign and verify support for 3072-bit or larger key sizes.
            *   Verify support for 3072-bit key size as part of secure boot
                implementation.
        *   ECDSA
            *   For OpenTitan, the minimum requirement is to support signature
                and verification on NIST P-256 and P-384 curves.
*   Key derivation function:
    *   Counter mode use of SP800-108, with HMAC as the PRF.

## Provisioning Requirements

OpenTitan used as a TPM has the following provisioning requirements:

*   **Unique Global Identifier**: Big integer value (up to 256b) used to
    facilitate tracking of the devices throughout their life cycle. The
    identifier is stored in One Time Programmable (OTP) storage during
    manufacturing.
*   **Endorsement Seed**: Generation of endorsement seed for RSA and ECC
    asymmetric operations. The seed is stored in encrypted or masked form with a
    key bound to the device's key manager.
*   **EK Certificate**: One EK Certificate for each asymmetric key type. Stored
    in the device. Additional requirements which may be fulfilled by an
    implementation relying on Ownership Transfer:
    *   The intermediate root certificate may be cross-signed by the Silicon
        Owner.
    *   The intermediate root certificate may only be used for a class of
        devices managed by the Silicon Owner.
    *   The intermediate root certificate must be chained to a well known root
        CA.
*   **Factory Firmware**: Baseline image with support for firmware update via
    SPI or I2C, and TPM 2.0 full or subset of commands required by the target
    platform.

## Packaging Constraints

*   Non-HDI packaging is required.
*   (Optional) TPM-spec compatible packaging.

## Additional Requirements

The requirements listed below are extracted from the
[TPM Profile (PTP) Specification version 1.03 revision 22](https://trustedcomputinggroup.org/resource/pc-client-platform-tpm-profile-ptp-specification/),
referred to as the PTP spec in the following sections.

### Storage Requirements

*   Size requirements as specified in section 3.6.1 of the PTP spec:
    *   Minimum of 8KB bytes of NV storage.
    *   Follow the storage guidance for pre-provisioned EK Certificates if these
        are available.

### External Peripherals

*   SPI device with support for TPM flow control protocol as specified in
    section 6.4.5 of the PTP spec. It is preferred to implement flow control in
    hardware.
*   I2C interface as specified in section 7.1 of the PTP doc.
*   GPIO: Additional pins used to implement platform security flows for a set of
    integration use cases.

## Relevant specs

*   https://trustedcomputinggroup.org/resource/tpm-library-specification/

*   https://trustedcomputinggroup.org/work-groups/trusted-platform-module/

<!-- Footnotes themselves at the bottom. -->

## Notes

[^1]: TCG requires membership in order to obtain TPM certification. There are
    additional compliance testing requirements. See TCG's certification portal
    for more details:
    https://trustedcomputinggroup.org/membership/certification/.
