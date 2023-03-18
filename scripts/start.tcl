vsim testbench -t 1ps -coverage  -voptargs=+acc -classdebug -suppress 3999 -suppress 7033 \
    -do "set StdArithNoWarnings 1; set NumericStdNoWarnings 1; log -r /*; run -all;" \
    +SRAM=/scratch/mciani/he-soc/hardware/working_dir/opentitan/hw/top_earlgrey/sw/tests/bootrom/rom_mapped_in_ram.elf -sv_lib work-dpi/ariane_dpi

set StdArithNoWarnings 1
set NumericStdNoWarnings 1
log -r /*

delete wave *
