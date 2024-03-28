# HMAC HWIP Technical Specification

[`hmac`](https://reports.opentitan.org/hw/ip/hmac/dv/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/hmac/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/hmac/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/hmac/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/hmac/code.svg)

# Overview

This document specifies HMAC hardware IP functionality. This module conforms to
the [OpenTitan guideline for peripheral device functionality.](../../../doc/contributing/hw/comportability/README.md)
See that document for integration overview within the broader OpenTitan top level system.


## Features

- HMAC supporting multiple digest sizes: SHA-2 256/384/512 hashing algorithm
- HMAC-SHA-2 and unkeyed SHA-2 dual mode
- Configurable key length 256/384/512/1024-bit secret key for HMAC mode
- 32 x 32-bit message buffer

## Description

[sha256-spec]: https://csrc.nist.gov/publications/detail/fips/180/4/final

The HMAC module is a [SHA-2][sha256-spec] hash-based authentication code generator to check the integrity of an incoming message and a signature signed with the same secret key.
It supports SHA-2 256/384/512 and 256/384/512/1024-bit keys in HMAC mode, so long as the key length does not exceed the block size of the configured SHA-2 mode, i.e., 1024-bit keys are not supported for SHA-2 256 where the block size is 512-bit.
It generates a different authentication code with the same message if the secret key is different.

This HMAC implementation is not hardened against side channel or fault injection attacks.
It is meant purely for hashing acceleration.
If hardened MAC operations are required, users should use either [KMAC](../kmac/README.md) or a software implementation.

The 1024-bit secret key is written in [`KEY_0`](doc/registers.md#key) to [`KEY_31`](doc/registers.md#key), and the key length relevant to the HMAC operation is configured in [`CFG.key_length`].
For example, to use a 256-bit secret key, [`CFG.key_length`] should be configured to 0x02 and then only secret key registers [`KEY_0`](doc/registers.md#key) to [`KEY_7`] are read and relevant for the HMAC operation.
The digest size required is configured in [`CFG.digest_size`].
The message to authenticate is written to [`MSG_FIFO`](doc/registers.md#msg_fifo) and the HMAC generates a 256/384/512-bit digest value (depending on the digest size configuration provided) which can be read from [`DIGEST_0`](doc/registers.md#digest) to [`DIGEST_7`](doc/registers.md#digest) for SHA-2 256, or from [`DIGEST_0`] to [`DIGEST_12`] for SHA-2 384, or from [`DIGEST_0`] to [`DIGEST_15`] for SHA-2 512.
The `hash_done` interrupt is raised to report to software that the final digest is available.

This module allows software to save and restore the hashing context so that different message streams can be interleaved; please check the [Programmer's Guide](doc/programmers_guide.md#saving-and-restoring-the-context) for more information.

The HMAC IP can run in SHA-only mode, whose purpose is to check the correctness of the received message.
The same digest registers above are used to represent the hash result.
SHA-2 mode does not use the given secret key.
It generates the same result with the same message every time.

The software does not need to provide the message length. The HMAC IP
will calculate the length of the message received between **1** being written to
[`CMD.hash_start`](doc/registers.md#cmd) and **1** being written to [`CMD.hash_process`](doc/registers.md#cmd).

This version does not have many defense mechanisms but is able to wipe internal variables such as the secret key, intermediate hash results H, digest and the message FIFO.
It does not wipe the software accessible 32x32b FIFO.
The software can wipe the variables by writing a 32-bit random value into [`WIPE_SECRET`](doc/registers.md#wipe_secret) register.
The internal variables will be reset to the written value.
This version of the HMAC does not have an internal pseudo-random number generator to derive the random number from the written seed number.

A later update may provide an interface for external hardware IPs, such as a key manager, to update the secret key.
It will also have the ability to send the digest directly to a shared internal bus.
