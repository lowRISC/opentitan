# `libbase`, the OpenTitan Standard Library

This subtree provides headers and libraries known collectively as `libbase`, which serve as OpenTitan's ersatz `libc`.

## Differences from a `libc`

`libbase` is not a `libc`, even though it implements a number of `libc` symbols, and should not be used as such.
`libbase` is, rather, a place for base libraries which may need to make use of more compiler/platform intrinsics than average, in order to present a safe, stable, and uesful interface that other parts of OpenTitan can rely on.

In general, a library exposing general utilities for working close to the hardware should live in this subtree: for example, a library providing `memcpy` and related symbols.
A library for talking to a particular peripheral, like a UART port, is a non-example.
