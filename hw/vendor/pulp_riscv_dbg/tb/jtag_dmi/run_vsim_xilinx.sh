#!/bin/bash
# Copyright 2020-2021 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51
#
# Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
# Andreas Kurth  <akurth@iis.ee.ethz.ch>

set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

if [ -z "$VIVADO_HOME" ]; then
    echo "Please set \$VIVADO_HOME to point to your Vivado installation."; exit 1;
fi

[ ! -z "$VSIM" ] || VSIM=vsim

bender script vsim -t test -t xilinx -t bscane \
    --vlog-arg="-svinputport=compat" \
    --vlog-arg="-override_timescale 1ns/1ps" \
    --vlog-arg="-suppress 2583" \
    --vlog-arg="+cover=sbecft" \
    > compile.tcl
echo 'return 0' >> compile.tcl
$VSIM -c -do 'exit -code [source compile.tcl]'

call_vsim() {
    vlog $VIVADO_HOME/data/verilog/src/glbl.v
    vlog $VIVADO_HOME/data/verilog/src/unisims/BSCANE2.v
    vlog $VIVADO_HOME/data/verilog/src/unisims/JTAG_SIME2.v
    echo "log -r /*; run -all" | $VSIM -c -coverage -voptargs='+acc +cover=sbecft' "$@" | tee vsim.log 2>&1
    grep "Errors: 0," vsim.log
}

call_vsim work.tb_jtag_dmi work.glbl
