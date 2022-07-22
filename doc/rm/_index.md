---
title: "Reference Manuals"
---

* [Comportability Definition and Specification]({{< relref "comportability_specification" >}})
* [Device Interface Function (DIF) Specification]({{< relref "device_interface_functions" >}})
* Tool Guides
   * [Topgen Tool]({{< relref "topgen_tool" >}}): Describes `topgen.py` and its Hjson format source. Used to generate rtl and validation files for top specific modules such as PLIC, Pinmux and crossbar.
   * [Register Tool]({{< relref "register_tool" >}}): Describes `regtool.py` and its Hjson format source. Used to generate documentation, rtl, header files and validation files for IP Registers and toplevel.
   * [Ipgen Tool]({{< relref "ipgen_tool" >}}): Describes `ipgen.py` and its Hjson control file. Used to generate IP blocks from IP templates.
   * [Crossbar Tool]({{< relref "crossbar_tool" >}}): Describes `tlgen.py` and its Hjson format source. Used to generate self-documentation, rtl files of the crossbars at the toplevel.
   * [Vendor-In Tool]({{< relref "vendor_in_tool" >}}): Describes `util/vendor.py` and its Hjson control file. Used to pull a local copy of code maintained in other upstream repositories and apply local patch sets.
* [FPGA Reference Manual]({{< relref "ref_manual_fpga.md" >}})
* [OpenTitan Continuous Integration]({{< relref "continuous_integration.md" >}})
