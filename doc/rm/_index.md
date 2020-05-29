---
title: "Reference Manuals"
---

* [Comportability Definition and Specification]({{< relref "comportability_specification" >}})
* [Device Interface Function (DIF) Specification]({{< relref "device_interface_functions" >}})
* Tool Guides
   * [Topgen Tool]({{< relref "topgen_tool" >}}): Describes `topgen.py` and its Hjson format source. Used to generate rtl and validation files for top specific modules such as PLIC, Pinmux and crossbar.
   * [Register Tool]({{< relref "register_tool" >}}): Describes `regtool.py` and its Hjson format source. Used to generate documentation, rtl, header files and validation files for IP Registers and toplevel.
   * [Crossbar Tool]({{< relref "crossbar_tool" >}}): Describes `tlgen.py` and its Hjson format source. Used to generate self-documentation, rtl files of the crossbars at the toplevel.
   * [Vendor-In Tool]({{< relref "vendor_in_tool" >}}): Describes `util/vendor.py` and its Hjson control file. Used to pull a local copy of code maintained in other upstream repositories and apply local patch sets.
* Coding Style Guides
  * [Verilog Coding Style](https://github.com/lowRISC/style-guides/blob/master/VerilogCodingStyle.md)
  * [Python Coding Style]({{< relref "python_coding_style.md" >}})
  * [Hjson Usage and Style Guide]({{< relref "hjson_usage_style.md" >}})
  * [Markdown Usage and Style Guide]({{< relref "markdown_usage_style.md" >}})
  * [C/C++ Style Guide]({{< relref "c_cpp_coding_style.md" >}})
  * [RISC-V Assembly Style Guide]({{< relref "asm_coding_style.md" >}})
* [FPGA Reference Manual]({{< relref "ref_manual_fpga.md" >}})
