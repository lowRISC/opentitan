# ROM_EXT Manifest Format

Based on the requirements outlined in [boot.md](./boot)

```
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                  ROM_EXT Manifest Identifier                  |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                            Reserved                           |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                                                               |
+                                                               +
|                                                               |
+                  Image Signature (3072 bits)                  +
|                                                               |
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~  break  ~~~~~~~~~~~~~~~~~~~~~~~~~~~
|                                                               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                          Image Length                         |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                         Image Version                         |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                                                               |
+                        Image Timestamp                        +
|                                                               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                 Signature Algorithm Identifier                |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                       Signature Exponent                      |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                    Usage Constraints (TBC)                    |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                            Reserved                           |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                                                               |
+                                                               +
|                                                               |
+                 Peripheral Lockdown Info (TBC)                +
|                                                               |
+                                                               +
|                                                               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                                                               |
+                                                               +
|                                                               |
+                Signature Public Key (3072 bits)               +
|                                                               |
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~  break  ~~~~~~~~~~~~~~~~~~~~~~~~~~~
|                                                               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                       Extension0 Offset                       |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                      Extension0 Checksum                      |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                       Extension1 Offset                       |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                      Extension1 Checksum                      |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                       Extension2 Offset                       |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                      Extension2 Checksum                      |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                       Extension3 Offset                       |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                      Extension3 Checksum                      |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                                                               |
+                                                               +
|                                                               |
+                           Code Image                          +
|                                                               |
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~  break  ~~~~~~~~~~~~~~~~~~~~~~~~~~~
|                                                               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
```

Notes:

*   All Offsets in the manifest are specified in bytes from the beginning of the
    `ROM_EXT Manifest Identifier` field.

*   All numeric and enumeration field values are stored little-endian. Fields
    below are noted as one of:

    *   a N-bit (signed or unsigned) numeric value;
    *   a N-bit enumeration value;
    *   a sequence of N-bit (signed or unsigned) numeric values; or
    *   a sequence of bytes.

    All numeric and enumeration values are stored little-endian.

    A byte only ever means an 8-bit data value, whose interpretation is
    undefined.

*   All fields below are 32-bit (4-byte) aligned unless otherwise specified.

    **Open Q**: The ordering below is still subject to alignment requirements
    for different fields, and may change in future.

*   The `Image Signature`, `ROM_EXT Signature Public Key` and `Image` are not
    shown to scale. This is denoted using `~~~ break ~~~` lines, which specify a
    truncation of field size displayed in the diagram, not that a new field has
    started.

    *   The Signature and Public Key are each 3072 bits long (they are
        notionally `int32_t[96]`s).

    *   The Code Image itself is variable length, where the length of the entire
        image (including the manifest) is given in the `Length` field.

*   Reserved areas are not documented below. Conforming implementations will not
    parse these fields, but will produce images where those bits are all zero.
    Reserved areas remain read-only, as they are signed as part of the image.
    Updating these fields will fail validation.

    Reserved fields have fixed size and unspecified alignment.

## Field Descriptions

1.  **ROM_EXT Manifest Identifier** This is a 32-bit enumeration value which is
    used by the Mask ROM to identify that an image with the above format is
    resident in flash. A particular Mask ROM version can only parse one ROM_EXT
    image format, there is no expected support for differing behaviour based on
    this field, beyond erroring when ROM_EXT images are missing from flash
    storage.

    This is used by any ROM_EXT image parsers to identify a ROM_EXT image.

1.  **Image Signature** This is a RSA 3k signature of all the fields that follow
    the signature. This a sequence of 32-bit values. There is no data in the
    image which is not signed, except the signature itself and the ROM_EXT
    manifest identifier.

    This is used by the Mask ROM during secure boot to validate that a ROM_EXT
    image has been produced by a Silicon Creator for this chip. This is also
    validated at other times, including during firmware update.

    If the image signature is a sequence of all zeroes, the image is unsigned.
    Unsigned images **must not** be booted.

1.  **Image Length** This denotes the Offset of the end of the image, in bytes.
    As with other offsets, this is calculated from the start of the `ROM_EXT
    Manifest Identifier` field. This is a 32-bit unsigned numeric value.

    This is used when signing, validating, and loading the image. This happens
    in the Mask ROM, as well as during firmware update.

1.  **Image Version** This is a version number for the ROM_EXT image. It
    is a 32-bit unsigned numeric value.

    **Open Q** How will we use this?

1.  **Image Timestamp** This is a Unix Timestamp describing when the ROM_EXT
    image was prepared, in seconds since 00:00:00 UTC on 1 January 1970 (the
    Unix Epoch). This is a 64-bit signed numeric value.

    This is not used by the Mask ROM when validating the image.

    *Alignment* This is 64-bit aligned.

1.  **Signature Algorithm Identifier** This identifies which algorithm has been
    used to sign the ROM_EXT Image. This is a 32-bit enumeration value.

    This is used when signing and validating the image. This happens in the
    Mask ROM, as well as during firmware update.

    `0x0` denotes an unsigned image. Unsigned images **must not** be booted.

    The initial version of the Mask ROM will support the following message
    digest algorithms:

    *   SHA2-265
    *   SHA2-384
    *   SHA2-512

    The specific signature scheme is as yet undefined, but will be based on
    RSA-3k, and one of the message digest algorithms above.

1.  **Signature Exponent** This is the RSA exponent to be used during the RSA
    3K Signature Scheme. This is a 32-bit numeric value.

    This is used when signing and validating the image. This happens in the
    Mask ROM, as well as during firmware update.

1.  **Usage Constraints** This is a 32-bit enumeration value which denotes what
    kinds of devices the ROM_EXT image may be used on.

    This is used by the Mask ROM to validate the image is running on the right
    kind of hardware.

    **Open Q** What possible values should this have?

1.  **Peripheral Lockdown Info** This is a 128-bit value which describes how
    some peripherals should be configured, before the write-enable bits for
    their configuration registers are cleared.

    This is used by the Mask ROM to configure specific peripherals (including,
    for example, pinmux and padctrl), in such a way that their configuration
    cannot be updated by the ROM_EXT or any other later firmware.

    **Open Q** We don't have inifnite space for this, so what configurations
    might we want to make and then lock?

    **Open Q** Required Alignment. Assuming 32-bit for the moment. We're
    currently tight for space, so this may turn into an Offset to later in the
    image.

1.  **Signature Public Key** This is a RSA 3k public key, as used by the image
    signature. This is a sequence of 32-bit values.

    This is used when signing and validating the image. This happens in the
    Mask ROM, as well as during firmware update.

1.  **Extensions** This is a sequence of 4 `(Offset, Checksum)` pairs. These
    allow for the ROM_EXT manifest format to be extended without redesigning the
    manifest entirely.

    Extensions are ignored by the Mask ROM. They may be parsed by the ROM_EXT
    itself and any later firmware stages.

    The Offset field denotes the byte offset in the image (including the
    manifest) where the extension can be found. The length of the respective
    data is defined by the extension itself (it can have either a static or
    variable length), but the manifest includes a Checksum field which must be
    used to store a checksum of the extension's data, using CRC32.

    Each Offset field is a 32-bit unsigned numeric value. Each Checksum field is
    a 32-bit numeric value.

    Extension pairs may be *allocated* a specific use. These fields should be
    treated as Reserved until they are allocated. Once an extension pair has an
    allocated use, it will not be used for any other use, unless the Manifest
    Image Identifier also changes (In this way, the Identifier also works as a
    versioning token for the manifest format). When an extension pair is
    allocated, the extension may define an alignment requirement for the its
    data. The extension's data must be at least byte-aligned.

    **Open Q** We could allocate more of these pairs, as we have quite a few
    bytes between the end of the last pair, and the first 256-byte-aligned
    address in the code image (see the Code Image field description.). Do we
    want to?

1.  **Code Image** This is a sequence of bytes that make up the code and data of
    the ROM_EXT image. This data will include any data required for Extensions.

    Execution begins at the address 128 (`0x80`) bytes beyond the first
    256-byte (`0x100`-byte) aligned offset at the start of the ROM_EXT code
    image (measuring the offset from the start of the ROM_EXT image). This
    leaves the possibility of the Mask ROM initializing `mtvec` with the first
    256-byte aligned offset in the ROM_EXT code image, before jumping into
    ROM_EXT code. This matches how Ibex boots.

    The total manifest length is currently `0x358` (856) bytes, so the first
    valid mtvec address is at offset `0x400` (1024) bytes from the beginning of
    the ROM_EXT image, and **the entry address is therefore `0x480` (1152) bytes
    from the beginning of the ROM_EXT image**.

    This does leave 168 (`0xa8`) bytes between the end of the manifest and the
    first valid mtvec. It is up to the image as to how this is used--it could be
    used for extension data or for routines. We could also reserve this space so
    the manifest can be extended later, but this is the intention of the
    Extension entries.

    **Open Q** Do we want to relax the requirement to match how ibex boots? We
    still want a static entry address so we don't have to validate that it is in
    bounds.

    **Open Q** Do we want to set `mtvec` before jumping to the ROM_EXT? This
    could cause double fault issues if ROM_EXT is not unlocked by the comparator
    before the jump happens.

### Data Not in the Header

*   `.data` + `.bss` section sizes, for establishing PMP regions. The PMP
    regions should be established by the ROM_EXT image as it sets up its own
    execution. This is not the responsibility of Mask ROM, as of yet.

*   `.idata` section offset, for copying initialization values into `.data`
    section in RAM, as again, this is the responsibility of the ROM_EXT image,
    not Mask ROM.

*   **Software Binding Tag** (aka **ROM_EXT Security Descriptor**)

    A 256-bit input is needed to help seed the CreatorRootKey, as part of
    preparing the key manager for later use.

    There was originally a proposal to have the party that prepared the image
    set the software binding tag explicitly, using a field in the manifest.
    However, we have chosen to always use a 256-bit digest of the ROM_EXT image
    itself.

    This means future ROM_EXTs can not read data encrypted with a previous
    ROM_EXT's key. A different ROM_EXT image will result in a different
    CreatorRootKey.

    This would have been used by the Mask ROM as an input for the key manager.

## Development Versions (Subject to Change)

**ROM_EXT Manifest Identifier**: `0x4552544F` (Reads "OTRE" when Disassembled --
OpenTitan ROM_EXT)

**Signature Algorithm Identifier**: TBC

**Signature Exponent**: TBC

**Signature Key Pair**: TBC. We will create a dummy key pair for development,
but this will not be used in production software.

**Extension Allocation**:

| Identifier   | Pair | Use           | Length | Alignment |
|--------------|------|---------------|--------|-----------|
| `0x4552544F` | 0    | *Unallocated* |        |           |
| `0x4552544F` | 1    | *Unallocated* |        |           |
| `0x4552544F` | 2    | *Unallocated* |        |           |
| `0x4552544F` | 3    | *Unallocated* |        |           |



## Software Deliverables

*   A C Library for parsing/extracting this image format on-device.

    This should take a Base Address, and parse using offsets from that, rather
    than a fixed address at the start of flash. This is so we can parse both
    ROM_EXT Slot A and Slot B using the same library.

*   A linker script (and assembly files) that can create a ROM_EXT ELF file
    containing all the code and data.

    The aim is to use absolute addresses for the stack and any in-RAM data, so
    that we end up mostly position-independent.

    **Open Q**: The ROM_EXT may need to be told which address the current image
    starts at when it boots.

*   A developer utility for taking a ROM_EXT ELF file and turning it into
    a correctly signed image for loading into either slot using the existing
    spiflash utility. This utility should also be able to validate a signed
    ROM_EXT image, to ensure that what we signed can be validated both on- and
    off-device.

    This utility will also have to take a Software Binding Tag and other
    metadata as input, for injecting into the image. It should almost certainly
    also create a receipt of the information it just signed, in a
    machine-parseable format.

*   (Potentially) a developer utility for assembling binary images that contain
    the entire contents of flash (ROM_EXT + BL0 + Owner Firmware + Persisted
    Data, for each of Slot A and B), for testing.

**Open Q** There are lots of open questions about position-independent code
issues and requirements, as we want to load the same image into Slot A or Slot
B, without having to re-link or re-compile the image (note we only have one
entry address). At least initially, we will only create images that can work
from Slot A, and later we will add support ensuring these images are linked in
a way that they can run from Slot B without modification.
