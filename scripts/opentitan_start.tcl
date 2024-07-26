# Copyright 2022 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

vsim testbench_asynch_astral -t 1ps -coverage  -voptargs=+acc -classdebug -suppress 3999 -suppress 8360 \
    -do "set StdArithNoWarnings 1; set NumericStdNoWarnings 1; log -r /*; run -all;" \
    +SRAM=${SRAM} +BOOTMODE=${BOOTMODE} -sv_lib work-dpi/elfloader
