#!/usr/bin/env bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# This is a file for the python `protocol` [1] tool which can produce an ASCII
# diagram for a protocol header.
#
# [1]: https://github.com/luismartingarcia/protocol

# We break some fields at a given length, so that the image format description
# is kept relatively short. I have been adding the break-line manually
# after-the-fact.
BROKEN_LENGTH=128


# The format here is lines of `<FIELD NAME>:<LENGTH IN BITS>,\n`.
# Lines containing only `\n` are allowed.
read -r -d '' FIELDS <<-FIELDS
ROM_EXT Manifest Identifier:32,
Reserved:32,
Image Signature (3072 bits):${BROKEN_LENGTH},

Image Length:32,
Image Version:32,
Image Timestamp:64,

Signature Algorithm Identifier:32,
Signature Exponent:32,
Usage Constraints (TBC):32,
Reserved:32,

Peripheral Lockdown Info (TBC):128,

Signature Public Key (3072 bits):${BROKEN_LENGTH},

Extension0 Offset:32,
Extension0 Checksum:32,
Extension1 Offset:32,
Extension1 Checksum:32,
Extension2 Offset:32,
Extension2 Checksum:32,
Extension3 Offset:32,
Extension3 Checksum:32,

Code Image:${BROKEN_LENGTH}
FIELDS

arg=$(echo "${FIELDS}" | tr -d '\n')

protocol --bits 32 "${arg}"
