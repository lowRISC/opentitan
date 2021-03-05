# Introduction

[OpenTitan Secure Boot][rom-ext-manifest] process consists of several stages.
On power-on reset, or wake-up from a deep sleep the execution enters the Mask
ROM, which is “baked” into the OpenTitan metal masks. This means that the Mask
ROM, once manufactured, cannot be updated. To add a degree of flexibility, in
particular to allow for a manufacturer specific configuration and facilities to
deliver security updates - OpenTitan design provisions the Extension ROM
(ROM_EXT) that lives in the flash memory.

ROM_EXT consists of a [manifest][1] and the image itself. When
the image is generated - the manifest data is "blank". The responsibility of
the ROM_EXT signer is to update the manifest, sign the image and add the
signature to it.

## Tooling

ROM_EXT signer is a host side tool that is written in Rust.

## Why Rust?

Rust has been chosen for the reach language and standard library features, as
well as incredible and versatile infrastructure. Rust's Cargo (build/packaging
system) and mature community driven database (crates.io), makes it easy and
cheap (in terms of effort) to find, integrate and use relevant functionality.

**This makes rust great for host side tooling**

# Current state

**Please note that this change is work in progress, and can be tracked via:
https://github.com/lowRISC/opentitan/issues/5232**

# Design

This tool consist of four major parts:

- Configuration file and parsing/deserealisation

- Image manipulation (updating the manifest)

- Image signing

- "Receipt" production

## Configuration file and parsing/deserialisation

The configuration file is in `.hjson` format, which is deserialised (turned
into Rust structures) using `hjson_serde` and `serde` crates.

Configuration file contains data for all of the fields that need updating in
the manifest before signing. Some manifest fields are unfeasible to specify
in the configuration file - these are binary blobs such as a private key in DER
format. Instead the file paths to these are specified.

Please note that some field values are known upfront, however other must be
obtained at runtime. Fields like (but not limited to) signature public modulus
and signature key public exponent are extracted separately.

Complex fields such as "Peripheral Lockdown Info" have a separate data
structure.

## Image manipulation (updating the manifest)

The manifest fields must be updated prior to signing, and then the signature
itself has to be written into the respective manifest field.

- Reads the binary image of the disk
- Reads and parses the configuration of the disk
- Reads the files specified in the configuration of the disk
- Updates the manifest fields
- Signs the updated image
- Updated the manifest signature field with the generated signature
- Writes the updated image to disk

## Image signing

Signing is done via mundane cryptographic library:
https://crates.io/crates/mundane

For signing details such as signing scheme, please see [manifest][1]
documentation.

## "Receipt" production

TBD


[1]: /sw/device/rom_exts/docs/manifest.md
