vsim testbench -t 1ps -voptargs=+acc -classdebug -suppress 3999 -suppress 7033 \
    +SRAM=/scratch/mciani/test/opentitan/hw/top_earlgrey/sw/tests/hmac_test/hmac_smoketest.elf -sv_lib work-dpi/ariane_dpi

set StdArithNoWarnings 1
set NumericStdNoWarnings 1
log -r /*

delete wave *
