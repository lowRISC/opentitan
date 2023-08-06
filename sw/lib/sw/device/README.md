# Device Libraries

## Overview

The OpenTitan repository contains device libraries which are used within our
Reference Firmware Images, and can (and should) be used by other OpenTitan
device software.

These are organised into the `sw/lib/sw/device` directory.

-   [`sw/lib/sw/device/base`](https://github.com/lowRISC/opentitan/tree/master/sw/lib/sw/device/base)
    contains the Base Libraries, including
    [freestanding C library headers](https://github.com/lowRISC/opentitan/tree/master/sw/lib/sw/device/base/freestanding).
    The Base Libraries are simple libraries that can be used by any other OpenTitan device software libraries.
-   `sw/lib/sw/device/arch` contains the definition header file for specific device
    configurations (for instance FPGA, Simulation, etc.).
-   [`sw/lib/sw/device/runtime`](https://github.com/lowRISC/opentitan/tree/master/sw/lib/sw/device/runtime)
    contains general libraries for more advanced on-device functionality
    (including logging, printing, and interacting with the RISC-V core).
-   [`sw/device/lib/testing`](../../../device/lib/testing/README.md)
    contains test library code. Test library code is any (reusable) code that
    could aid in the writing of smoke, IP integration, or system-level tests,
    that is a layer of above the DIFs. In other words, this code may make use
    of the DIFs to actuate the hardware, and chip-level test code may make use
    of this code to actuate the DIFs.
