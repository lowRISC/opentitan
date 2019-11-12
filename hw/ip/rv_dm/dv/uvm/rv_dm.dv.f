-f ${PRJ_DIR}/hw/ip/rv_dm/rtl/deps.f

-f ${PRJ_DIR}/hw/ip/rv_dm/rtl/rv_dm.f

${PRJ_DIR}/hw/ip/tlul/dv/xbar_if.sv
${PRJ_DIR}/hw/ip/tlul/dv/device_sram.sv

${PRJ_DIR}/hw/ip/rv_dm/dv/jtag_if.sv

+incdir+${PRJ_DIR}/hw/ip/rv_dm/dv
${PRJ_DIR}/hw/ip/rv_dm/dv/rjtag_pkg.sv

// ${PRJ_DIR}/hw/ip/rv_dm/dv/test/riscv_jtag_sba_test.sv

${PRJ_DIR}/hw/ip/rv_dm/dv/tb.sv
