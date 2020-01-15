# The OpenTitan DIF Library

A DIF is a "Device Interface Function". DIFs are low-level routines for
accessing the hardware functionality directly, and are agnostic to the
particular environment or context they are called from. The intention is that
DIFs can be used during design verification, and during early silicon
verification, and by the high-level driver software in production firmware.

This subtree provides headers and libraries known collectively as the DIF
libraries.

There is one DIF library per hardware IP, and each one contains the DIFs
required to actuate all of the specification-required functionality of the
hardware they are written for.
