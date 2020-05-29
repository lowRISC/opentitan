---
title: "OpenTitan Software"
---

This is the landing spot for software documentation within the OpenTitan project.
Primarily these are README files about different software components.
More description and information can be found within the [Reference Manual]({{< relref "doc/rm" >}}) and [User Guide]({{< relref "doc/ug" >}}) areas.

## Software READMEs

* General build instruction [README.md]({{< relref "sw/README.md" >}})
* Hello World example [README.md]({{< relref "sw/device/examples/hello_world/README.md" >}})
* Boot ROM Overview [README.md]({{< relref "sw/device/boot_rom/README.md" >}})
* SPI Flash [README.md]({{< relref "sw/host/spiflash/README.md" >}})
* Device Tests [README.md]({{< relref "sw/device/tests/README.md" >}})
* OpenTitan Software Library
  * Standard Library [README.md]({{< relref "sw/device/lib/base/README.md" >}})
  * Freestanding C Headers [README.md]({{< relref "sw/device/lib/base/freestanding/README.md" >}})
  * Runtime Library [README.md]({{< relref "sw/device/lib/runtime/README.md" >}})
  * Device-specific Symbols [README.md]({{< relref "sw/device/lib/arch/README.md" >}})
  * DIF Library [README.md]({{< relref "sw/device/lib/dif/README.md" >}})
* CoreMark benchmark [README.md]({{< relref "sw/device/benchmarks/coremark/README.md" >}})
* Vendor in code see [HW vendor User Guide]({{< relref "doc/ug/vendor_hw.md" >}})
  * [CoreMark](https://github.com/eembc/coremark)
  * [RISC-V Compliance](https://github.com/riscv/riscv-compliance)
  * [Google Test](https://github.com/google/googletest)
  * [Cryptoc](https://chromium.googlesource.com/chromiumos/third_party/cryptoc/)
