vsim testbench -t 1ps -voptargs=+acc -classdebug -suppress 3999 -suppress 7033 \
    +OT_STRING=/scratch/mciani/he-soc/hardware/working_dir/opentitan/hw/top_earlgrey/sw/tests/crypto/crypto_test.elf -sv_lib work-dpi/ariane_dpi

set StdArithNoWarnings 1
set NumericStdNoWarnings 1
log -r /*

delete wave *
