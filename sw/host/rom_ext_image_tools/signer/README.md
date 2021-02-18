# Introduction

[OpenTitan Secure Boot][rom-ext-manifest] process consists of several stages.
On power-on reset, or wake-up from a deep sleep the execution enters the Mask
ROM, which is “baked” into the OpenTitan metal masks. This means that the Mask
ROM, once manufactured, cannot be updated. To add a degree of flexibility, in
particular to allow for a manufacturer specific configuration and facilities to
deliver security updates - OpenTitan design provisions the Extension ROM
(ROM_EXT) that lives in the flash memory.

ROM_EXT consists of a [manifest][rom-ext-manifest] and the image itself. When
the image is generated - the manifest data is "blank". The responsibility of
ROM_EXT signer is to update the manifest, sign the image and add the
signature to it.

## Tooling

ROM_EXT signer is a host side tool that is written in Rust.

## Why Rust?

Rust has been chosen for the reach language and standard library features, as
well as incredible and versatile infrastructure. Rust's Cargo (build/packaging
system) and mature community driven database (crates.io), makes it easy and
cheap (in terms of effort) to find, integrate and use relevant functionality.

** This makes rust great for host side tooling **

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
the manifest before signing.

Please note that signature key modulus and signature key public exponent are
extracted separately. The configuration file has a link to the private key,
and public key is extracted from it via `ring` library.

Generic (u32 or u64) integers are defines as an array. This is done to make
updating the manifest easier. Complex fields such as "Peripheral Lockdown
Info" have a separate data structure, and are spliced into the image separately.

## Image manipulation (updating the manifest)

Reads the binary image of the disk. It uses the parsed configuration to
update the manifest before signing, and is responsible for generating the signed
file.

## Image signing

TODO

## "Receipt" production

TODO

<!-- Links -->
[csm-secure-boot]: {{< relref "doc/security/specs/secure_boot" >}}
[rom-ext-manifest]: {{< relref "sw/device/rom_exts/docs/manifest" >}}
