---
title: "Universal 2nd-Factor Security Key"
---

When used as a security key, OpenTitan implements the Universal 2nd Factor (U2F)
authentication standard, using a Universal Serial Bus (USB) 1.1 interface to
communicate with host devices. U2F requires the implementation of a
challenge-response authentication protocol based on public key cryptography. The
security key is provisioned with a unique identity in the form of an asymmetric
key, which may be self-endorsed by a certificate issued at manufacturing time.

When used as a security key, OpenTitan shall meet the FIDO Authenticator
security goals and measures described in the [FIDO Security Reference v1.2][1]
specification. See [Universal 2nd Factor (U2F) Overview v1.2][2] for more
details on the functional requirements of this use case.

### Certification Requirements

*   [BSI-PP-CC-0096-V3-2018][3] FIDO Universal Second Factor (U2F)
    Authenticator. The minimum assurance level for this Protection Profile (PP)
    is EAL4 augmented. This PP supports composite certification on top of the
    Security IC Platform Protection Profile with Augmentation Packages,
    BSI-CC-PP-0084-2014 (referred to as PP84).
*   [FIPS 140-2 L1 + L3 physical][4] certification is required for some use
    cases.

### Minimum Crypto Algorithm Requirements

The current target for all crypto is at least 128-bit security strength. This is
subject to change based on the implementation timeline of any given
instantiation of OpenTitan. It is expected that a future implementation may be
required to target a minimum of 192-bit or 256-bit security strength.

*   TRNG:
    *   Entropy source for ECDSA keypair generation (seed and nonce).
    *   (optional) Symmetric MAC key generation.
*   Asymmetric Key Algorithms:
    *   ECDSA: Signature and verification on NIST P-256 curve for identity and
        attestation keys.
    *   RSA-3072: Secure boot signature verification. Used to verify the
        signature of the device's firmware.
*   Symmetric Key Algorithms:
    *   AES-CTR:
        -   (optional) Used to wrap a user private key in a key handle.
            Implementation dependent.
    *   HMAC-SHA256:
        -   For application key handle generation.
*   Hash Algorithms:
    *   SHA-256:
        -   Code and hardware measurements used in internal secure boot
            implementation.
        -   (optional) For key handle generation. Implementation dependent.
        -   (optional) Attestation cert generation, if generated on the fly.

### Provisioning Requirements

OpenTitan used as a security key has the following provisioning requirements:

*   Unique Global Identifier: Non-Cryptographic big integer value (up to 256b)
    used to facilitate tracking of the devices throughout their life cycle. The
    identifier is stored in One Time Programmable (OTP) storage during
    manufacturing.
*   Attestation Key: Unique cryptographic identity used for attestation
    purposes.
*   Self-Signed Attestation Certificate: Self signed certificate and extracted
    at manufacturing time for registration purposes. U2F backend servers can
    create an allow-list of certificates reported by the secure key
    manufacturer, and use them to perform authenticity checks as part of the
    registration flow.
*   Factory Firmware: Baseline image with support for firmware update via USB,
    and the USB HID U2F command spec.

### Additional Requirements

*   Physical Presence GPIO: U2F requires physical user presence checks for
    registration and authentication flows. This is implemented either via a push
    button or capacitive touch sensor connected to an input GPIO pin.
    *   At least 2 PWM peripherals can facilitate implementation of capacitive
        touch sensor IO operations.
*   Status LEDs GPIO: The security key may use LEDs to provide feedback to the
    user. This requires up to 4 additional output GPIO pins.
*   USB HID U2F Stack: The security key communicates with host devices via a USB
    HID protocol. OpenTitan shall meet the USB 1.1 connectivity and protocol
    requirements to interface with the host.

### Relevant specs

https://fidoalliance.org/specifications/download/

[1]: https://fidoalliance.org/specs/fido-u2f-v1.2-ps-20170411/fido-security-ref-v1.2-ps-20170411.html
[2]: https://fidoalliance.org/specs/fido-u2f-v1.2-ps-20170411/fido-u2f-overview-v1.2-ps-20170411.html
[3]: https://www.commoncriteriaportal.org/files/ppfiles/pp0096V3b_pdf.pdf
[4]: https://en.wikipedia.org/wiki/FIPS_140-2#Security_levels
