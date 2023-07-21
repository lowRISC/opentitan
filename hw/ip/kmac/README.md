# KMAC HWIP Technical Specification

{{#block-dashboard kmac}}

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
- 1600b of internal state (internally represented in two shares for 1st-order masking)
- Performance goals of >= 72 Mb/s @ 100MHz (when entropy is available always)
    - SHA3-512: roughly 66 MB/s at most
    - SHA3-224: 120 MB/s at most
- Implement 1st-order masked Keccak permutations for Side-Channel Analysis (SCA) protection

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
