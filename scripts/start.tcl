vsim testbench_asynch -t 1ps -coverage  -voptargs=+acc -classdebug -suppress 3999 -suppress 8360 \
    -do "set StdArithNoWarnings 1; set NumericStdNoWarnings 1; log -r /*; run -all;" \
     +SRAM=../hw/top_earlgrey/sw/tests/preboot_code/preboot_code.elf -sv_lib work-dpi/ariane_dpi
