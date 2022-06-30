---
title: "Fpvgen: Initial FPV testbench generation tool"
---

# Overview

`fpvgen` is a Python tool that can be used to generate the initial boilerplate code for an FPV testbench.
It takes as input a SystemVerilog module file representing the top-level of an IP to be tested with FPV, and generates the following folders and files in the output directory (which defaults to `../fpv` with respect to the module file provided):
```console
.
├── fpv // default output folder
│   ├── <ip-name>_fpv.core
│   ├── tb
│   │   ├── <ip-name>_bind_fpv.sv
│   │   └── <ip-name>_fpv.sv
│   └── vip
│       └── <ip-name>_assert_fpv.sv
└── rtl // folder containing the SV module file
    ├── <ip-name>.sv
    ...
```
The `<ip-name>_fpv.sv` is the FPV testbench that can be used to instantiate different parameterizations of the DUT to be tested.
`<ip-name>_bind_fpv.sv` contains the bind statement which binds the verification IP `<ip-name>_assert_fpv.sv` to all DUT instances.
If the IP is flagged as being comportable using the `-c` switch, the CSR FPV assertions are bound to the module as well.

# Examples
Generating a non-comportable IP can be done as follows (using the LFSR as an example):
```console
util/fpvgen.py hw/ip/prim/rtl/prim_lfsr.sv
```

If the IP is comportable, only the `-c` switch has to be added.
E.g., using the `pinmux` comportable IP as an example:
```console
util/fpvgen.py -c hw/ip/pinmux/rtl/pinmux.sv
```

If needed, the default output directory can be overridden using the `-o` switch.

# Help Output
This is the help output from the tool (switch `-h`).
```console
usage: fpvgen [-h] [-o OUTDIR] [-c] file

        Boilerplate code generator for FPV testbenches. Can be used for
        comportable or non-comportable IPs.

        The generator creates the FuseSoC core file and two additional
        subfolders 'tb' and 'vip' in the output directory. It will place stubs
        for the testbench and bind files into the 'tb' subfolder, and a stub for
        the FPV assertions into the 'vip' (verification IP) subfolder.

        The generator needs the path to the top-level module of the IP to be
        tested. E.g., suppose we would like to generate an FPV testbench for a
        FIFO primitive located at 'hw/ip/prim/rtl/prim_fifo_sync.sv' we can
        invoke the generator as follows:

        util/fpvgen.py hw/ip/prim/rtl/prim_fifo_sync.sv

        By default, the output directory is assumed to be '../fpv' with respect
        to the toplevel module, but this can be overriden using the -eo switch.

        Further if the IP is comportable, this can be indicated using the -c
        switch, which causes the generator to add a bind statement for the CSR
        FPV assertions in the testbench.

positional arguments:
  file                  Relative path to the SystemVerilog file of the module
                        for which the code shall be generated. This can be a
                        primitive or a comportable IP (for which the -c switch
                        should be set).

optional arguments:
  -h, --help            show this help message and exit
  -o OUTDIR, --outdir OUTDIR
                        Path where to place the testbench code. This is
                        defaults to '../fpv' w.r.t. to the module path. For
                        instance, if the module path is
                        'hw/ip/mymod/rtl/mymod.sv', the FPV testbench would be
                        generated under hw/ip/mymod/fpv.
  -c, --is_cip          Indicates whether this is a comportable IP. If yes,
                        FPV assertions for the TL-UL interface and CSRs are
                        automatically bound in the testbench. Note however
                        that these CSR assertions need to be generated
                        separately using the regtool automation.
```
