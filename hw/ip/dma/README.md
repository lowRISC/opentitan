# DMA Controller (dma)

The integrated version of OpenTitan root of trust may provide security
services to the system on chip (SoC) such as:

-   Encryption or decryption of data blobs.
-   Cryptographic hashing of data blobs.
-   Key derivation.
-   Random seed generation service.
-   Public key signing.
-   Public key verification.
-   Root of trust for measurement, reporting and storage.
-   Secure firmware update.
-   Access to secure storage.
-   Mutual authentication / attestation services.
-   SoC security monitoring / book-keeping services.
-   Debug authentication / unlock service.

Such operations require movement of bulk data from SoC / system memory
to the OpenTitan (OT) private memory and vice-versa. The Secure DMA
controller block provides OpenTitan with the ability to move data
blobs securely in and out of the OpenTitan memory while offloading the
Ibex core to focus on security critical tasks. The secure DMA provides
a hardware isolation layer between OpenTitan and the rest of the SoC.
It provides the hardware enforcement of security properties through well
defined isolation & access control techniques, hardware based checking
and other protection mechanisms. Note that depending upon the use case, it
is expected that the SoC provides proper security mechanisms for code /
data protections such as access control mechanisms, encrypted and
integrity protected memory regions, etc.

An example scenario where a secure DMA could potentially be used is
firmware controlled secure boot operation:

-   Configure the DMA to move a signed firmware image (or a manifest) into the OT
    DMA enabled memory.
-   OT performs a digital cryptographic hash operation and a signature-based
    verification of the firmware image / manifest.
-   If the digital signature verification passes, the DMA is configured to move
    the firmware to a protected location within the SoC secured by
    access control to prevent further modification.
-   Enable other firmware-based processing elements to boot from this
    secure location.

Additional efficiency benefits can be derived by supporting optional
smart inline operations within the DMA controller such as on-the-fly hashing, on-the-fly
encryption, etc. Inline operations would
additionally remove size restrictions on data to be hashed and could
keep data that gets hashed or encrypted physically confidential. Inline
operations are a potential extension for a next generation of the DMA
Controller and are described in more detail in [*Extension: Inline
Operations*](./doc/theory_of_operation.md#extension-inline-operations).

The DMA controller shall be used in conjunction with the
[*OpenTitan mailbox interface*](): The Ibex CPU reads
and parses pre-defined mailbox command objects, sanitizes DMA parameters
(such as the desired DMA operation and SoC memory addresses) from an
object, and configures the DMA controller accordingly. Note that
addresses here are treated as IO virtual addresses. Deliberately, there
is no hardware interface that would allow the SoC to control the DMA
Controller. Please refer to the '[*Access to SoC address
space*]()'
page for more details on handling of SoC level memory operations.
