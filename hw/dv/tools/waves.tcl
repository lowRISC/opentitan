# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

#
# Generic TCL included by tool-specific scripts when wave dumping is
# enabled.
#
# This is used by all supported simulators, and the driver scripts
# (dvsim.py) need to make sure that we don't ask for an unsupported
# dumping format (SHM with VCS, for example).
#

set dump_fmt none
if {[info exists ::env(DUMP_FMT)]} {
    set dump_fmt "$::env(DUMP_FMT)"
} else {
    puts "ERROR: No DUMP_FMT specified for wave dumping."
    quit
}

set tb_top "tb"
if {[info exists ::(TB_TOP)]} {
    set tb_top "$::env(TB_TOP)"
}

if {"$dump_fmt" == "fsdb"} {
    # The fsdbDumpvars +all command dumps everything: memories,
    # MDA signals, structs, unions, power and packed structs.
    puts "Dumping waves with VERDI to waves.fsdb"
    fsdbDumpfile  "waves.fsdb"
    fsdbDumpvars  0 $tb_top +all
    fsdbDumpSVA   0 $tb_top
} elseif {"$dump_fmt" == "shm"} {
    puts "Dumping waves in SHM format to waves.shm"
    database -open -default -shm "waves.shm"
    probe "$tb_top" -all -depth all -shm
} elseif {"$dump_fmt" == "vpd"} {
    puts "Dumping waves in VCD+ format to waves.vpd"
    dump -file "waves.vpd"
    dump -add "$tb_top" -depth 0 -aggregates -scope "."
} else {
    puts "ERROR: Unknown dump format: ${dump_fmt}"
    quit
}
