#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Generates boilerplate code for the FPV testbench setup."""

import argparse
from pathlib import Path

from mako.template import Template

import fpvgen.sv_parse as sv_parse


def main():
    parser = argparse.ArgumentParser(
        prog="fpvgen",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description="""\
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
        FPV assertions in the testbench.""",
        add_help=True)
    parser.add_argument(
        'file',
        type=Path,
        help="""Relative path to the SystemVerilog file of the module for which
        the code shall be generated. This can be a primitive or a comportable IP
        (for which the -c switch should be set)."""
    )

    parser.add_argument(
        '-o',
        '--outdir',
        type=Path,
        default=None,
        help="""Path where to place the testbench code. This is defaults to
        '../fpv' w.r.t. to the module path. For instance, if the module path is
        'hw/ip/mymod/rtl/mymod.sv', the FPV testbench would be generated under
        hw/ip/mymod/fpv. """
    )
    parser.add_argument(
        '-c',
        '--is_cip',
        action="store_true",
        default=False,
        help="""Indicates whether this is a comportable IP. If yes, FPV
        assertions for the TL-UL interface and CSRs are automatically bound in
        the testbench. Note however that these CSR assertions need to be
        generated separately using the regtool automation.""")

    args = parser.parse_args()

    mod_path = args.file
    if not mod_path.is_file() or mod_path.suffix != ".sv":
        print("Error: %s is not a module or does not exist" % str(mod_path))
        return 1

    if not args.outdir:
        # the default output path is ../fpv with
        # respect to the module location
        parentpath = mod_path.absolute().parent.parent
        outpath = parentpath.joinpath("fpv")
    else:
        outpath = args.outdir

    print("Output path is: %s" % outpath)

    dut = sv_parse.parse_file(mod_path)
    dut.is_cip = args.is_cip

    # always include the prims
    dut.deps += ["lowrisc:prim:all"]

    if args.is_cip:
        # for TL-UL assertions
        dut.deps += ["lowrisc:ip:tlul"]
        # in this case the parent directory is
        # likely the correct basename of the IP
        dut.deps += ["lowrisc:ip:" + parentpath.stem]

    fpvgen_dir = Path(__file__).parent.joinpath('fpvgen')
    tpls = [('tb.sv.tpl', 'tb', '_tb.sv'),
            ('bind_fpv.sv.tpl', 'tb', '_bind_fpv.sv'),
            ('assert_fpv.sv.tpl', 'vip', '_assert_fpv.sv'),
            ('fusesoc.core.tpl', '.', '_fpv.core')]

    for rel_tpl_path, out_subdir, out_suffix in tpls:
        tpl_path = fpvgen_dir.joinpath(rel_tpl_path)
        out_path = outpath.joinpath(out_subdir, mod_path.stem + out_suffix)

        print(f"Generating {out_path}")
        out_path.parent.mkdir(parents=True, exist_ok=True)
        tpl = Template(tpl_path.read_text())
        out_path.write_text(tpl.render(dut=dut))

    return 0


if __name__ == "__main__":
    main()
