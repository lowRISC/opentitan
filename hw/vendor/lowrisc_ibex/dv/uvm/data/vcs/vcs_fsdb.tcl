# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# TCL file invoked from VCS's simv at run-time using this: -ucli -do <this file>

set dump_waves 0
if {[info exists ::env(WAVES)]} {
    set dump_waves "$::env(WAVES)"
}

if {"$dump_waves" == 1} {
    # The basename (without extension) of the file where we should dump waves.
    # Defaults to "waves".
    set dump_base "waves"
    if {[info exists ::(DUMP_BASE)]} {
        set dump_base "$::env(DUMP_BASE)"
    }

    # The name of the top-level testbench. Defaults to "tb" if not defined in
    # environment
    set tb_top "tb"
    if {[info exists ::(TB_TOP)]} {
        set tb_top "$::env(TB_TOP)"
    }

    if {[info exists ::env(VERDI_HOME)]} {
        # Looks like we've got a Verdi licence. The fsdbDumpvars command tells
        # VCS to dump everything: memories, MDA signals, structs, unions, power
        # and packed structs.
        puts "Dumping waves with VERDI to ${dump_base}.fsdb"
        fsdbDumpfile  "${dump_base}.fsdb"
        fsdbDumpvars  0 $tb_top +all
        fsdbDumpSVA   0 $tb_top
    } else {
        # We don't have Verdi, so use standard dumping format (VCD+)
        puts "Dumping waves in VCD+ format to ${dump_base}.vpd"
        dump -file "${dump_base}.vpd"
        dump -add "$tb_top" -depth 0 -aggregates -scope "."
    }
}

run
quit
