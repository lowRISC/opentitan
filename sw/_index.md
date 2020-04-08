---
title: "OpenTitan Software"
---

This is the landing spot for software documentation within the OpenTitan project.
More description and information can be found within the [Reference Manual]({{< relref "doc/rm" >}}) and [User Guide]({{< relref "doc/ug" >}}) areas.

There are two major parts to the OpenTitan software stack:

* The _device_ software, which runs on the OpenTitan platform.
* The _host_ software, which is run on a host device and interacts with an OpenTitan device.

## OpenTitan Software API Documentation

The [OpenTitan Software API Documentation](/sw/apis/) contains automatically generated documentation for the public software APIs.
This includes the Device Interface Functions (DIFs).

All DIFs are also documented on their respective [Hardware IP Specification]({{< relref "hw" >}})

## Software READMEs

{{% sectionContent %}}

## Vendor in code see [HW vendor User Guide]({{< relref "doc/ug/vendor_hw.md" >}})

* [CoreMark](https://github.com/eembc/coremark)
* [RISC-V Compliance](https://github.com/riscv/riscv-compliance)
* [Google Test](https://github.com/google/googletest)
* [Cryptoc](https://chromium.googlesource.com/chromiumos/third_party/cryptoc/)
