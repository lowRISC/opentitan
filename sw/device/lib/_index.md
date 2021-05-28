---
title: "Device Libraries"
---

## Overview

The OpenTitan repository contains device libraries which are used within our
Reference Firmware Images, and can (and should) be used by other OpenTitan
device software.

These are organised into the `sw/device/lib` directory.

-   [`sw/device/lib/base`]({{< relref "sw/device/lib/base/README.md" >}})
    contains the Base Libraries, including
    [freestanding C library headers]({{< relref "sw/device/lib/base/freestanding/README.md" >}}).
    The Base Libraries are simple libraries that can be used by any other OpenTitan device software libraries.
-   [`sw/device/lib/dif`]({{< relref "sw/device/lib/dif/README.md" >}})
    contains the
    [Device Interface Functions]({{< relref "doc/rm/device_interface_functions.md" >}}).
-   [`sw/device/lib/arch`]({{< relref "sw/device/lib/arch/README.md" >}})
    contains the libraries to be used on specific device configurations (for
    instance FPGA, Simulation, etc.).
-   [`sw/device/lib/runtime`]({{< relref "sw/device/lib/runtime/README.md" >}})
    contains general libraries for more advanced on-device functionality
    (including logging, printing, and interacting with the RISC-V core).

## Documentation Index

{{% sectionContent %}}
