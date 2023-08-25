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

- HMAC with SHA256 hash algorithm
- HMAC-SHA256, SHA256 dual mode
- 256-bit secret key
- 16 x 32-bit Message buffer

## Description

[sha256-spec]: https://csrc.nist.gov/publications/detail/fips/180/4/final

The HMAC module is a [SHA-256][sha256-spec] hash based authentication code
generator to check the integrity of an incoming message and a signature signed
with the same secret key. It generates a different authentication code with the
same message if the secret key is different.

This HMAC implementation is not hardened against side channel or fault injection attacks.
It is meant purely for hashing acceleration.
If hardened MAC operations are required, users should use either [KMAC](../kmac/README.md) or a software implementation.

The 256-bit secret key is written in [`KEY_0`](doc/registers.md#key) to [`KEY_7`](doc/registers.md#key).
The message to authenticate is written to [`MSG_FIFO`](doc/registers.md#msg_fifo) and the HMAC generates a 256-bit digest value which can be read from [`DIGEST_0`](doc/registers.md#digest) to [`DIGEST_7`](doc/registers.md#digest).
The `hash_done` interrupt is raised to report to software that the final digest is available.

The HMAC IP can run in SHA-256-only mode, whose purpose is to check the
correctness of the received message. The same digest registers above are used to
represent the hash result. SHA-256 mode doesn't use the given secret key. It
generates the same result with the same message every time.

The software doesn't need to provide the message length. The HMAC IP
will calculate the length of the message received between **1** being written to
[`CMD.hash_start`](doc/registers.md#cmd) and **1** being written to [`CMD.hash_process`](doc/registers.md#cmd).

This version doesn't have many defense mechanisms but is able to
wipe internal variables such as the secret key, intermediate hash results
H, digest and the message FIFO. It does not wipe the software accessible 16x32b FIFO.
The software can wipe the variables by writing a 32-bit random value into
[`WIPE_SECRET`](doc/registers.md#wipe_secret) register. The internal variables will be reset to the written
value. This version of the HMAC doesn't have a internal pseudo-random number
generator to derive the random number from the written seed number.

A later update may provide an interface for external hardware IPs, such as a key
manager, to update the secret key. It will also have
the ability to send the digest directly to a shared internal bus.
