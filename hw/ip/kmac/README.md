# KMAC HWIP Technical Specification

[`kmac/masked`](https://reports.opentitan.org/hw/ip/kmac_masked/dv/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/kmac/masked/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/kmac/masked/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/kmac/masked/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/kmac/masked/code.svg)

[`kmac/unmasked`](https://reports.opentitan.org/hw/ip/kmac_unmasked/dv/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/kmac/unmasked/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/kmac/unmasked/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/kmac/unmasked/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/kmac/unmasked/code.svg)

# Overview

This document specifies the Keccak Message Authentication Code (KMAC) and Secure Hashing Algorithm 3 (SHA3) hardware IP functionality.
This module conforms to the OpenTitan guideline for peripheral device functionality.
See that document for integration overview within the broader OpenTitan top level system.

## Features

- Support for SHA3-224, 256, 384, 512, SHAKE[128, 256] and cSHAKE[128, 256]
- Support byte-granularity on input message
- Support 128b, 192b, 256b, 384b, 512b of the secret key length in KMAC mode
- Support arbitrary output length for SHAKE, cSHAKE, KMAC
- Support customization input string S, and function-name N up to 36 bytes total
- 64b x 10 depth Message FIFO
- First-order masking of the Keccak core using domain-oriented masking (DOM) to deter side-channel analysis (SCA), can optionally be disabled using compile-time Verilog parameters (for more details see [Keccak Round below](doc/theory_of_operation.md#keccak-round))
- 1600b of internal state (internally represented in two shares if masking is enabled)
- Performance (at 100 MHz):
  - SHA3-224: 2.93 B/cycle, 2.34 Gbit/s (masking disabled) - 1.19 B/cycle, 952 Mbit/s (DOM)
  - SHA3-512: 1.47 B/cycle, 1.18 Gbit/s (masking disabled) - 0.59 B/cycle, 472 Mbit/s (DOM)

## Description

The KMAC module is a Keccak based message authentication code generator to check the integrity of an incoming message and a signature signed with the same secret key.
The secret key length can vary up to 512 bits.

The KMAC generates at most 1600 bits of the digest value at a time which can be read from the STATE memory region.
There's a way for the software to read more digest values by manually running the Keccak rounds.
The details of the operation are described in the [SHA3 specification, FIPS 202](https://csrc.nist.gov/publications/detail/fips/202/final) known as _sponge construction_.

The KMAC HWIP also performs the SHA3 hash functions without the authentication, whose purpose is to check the correctness of the received message.
The KMAC IP supports various SHA3 hashing functions including SHA3 Extended Output Function (XOF) known as SHAKE functions.

The KMAC HWIP implements a defense mechanism to deter SCA attacks.
It is expected to protect against 1st-order SCA attacks by implementing masked storage and [Domain-Oriented Masking (DOM)](https://eprint.iacr.org/2017/395.pdf) inside the Keccak function.
