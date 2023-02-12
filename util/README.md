# Reference Manuals

* [Comportability Definition and Specification](../doc/contributing/hw/comportability/README.md)
* [Device Interface Function (DIF) Specification](../doc/contributing/sw/device_interface_functions.md)
* Tool Guides
   * [Topgen Tool](./topgen/README.md): Describes `topgen.py` and its Hjson format source. Used to generate rtl and validation files for top specific modules such as PLIC, Pinmux and crossbar.
   * [Register Tool](./reggen/README.md): Describes `regtool.py` and its Hjson format source. Used to generate documentation, rtl, header files and validation files for IP Registers and toplevel.
   * [Ipgen Tool](./ipgen/README.md): Describes `ipgen.py` and its Hjson control file. Used to generate IP blocks from IP templates.
   * [Crossbar Tool](./tlgen/README.md): Describes `tlgen.py` and its Hjson format source. Used to generate self-documentation, rtl files of the crossbars at the toplevel.
   * [Vendor-In Tool](./doc/vendor.md): Describes `util/vendor.py` and its Hjson control file. Used to pull a local copy of code maintained in other upstream repositories and apply local patch sets.
* [FPGA Reference Manual](../doc/contributing/fpga/ref_manual_fpga.md)
* [OpenTitan Continuous Integration](../doc/contributing/ci/README.md)
