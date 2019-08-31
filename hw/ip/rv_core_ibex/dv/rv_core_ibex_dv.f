${PRJ_DIR}/hw/ip/prim/rtl/prim_assert.sv
${PRJ_DIR}/hw/ip/prim_generic/rtl/prim_generic_clock_gating.sv
${PRJ_DIR}/hw/ip/prim_xilinx/rtl/prim_xilinx_clock_gating.sv
${PRJ_DIR}/hw/ip/prim/abstract/prim_clock_gating.sv
${PRJ_DIR}/hw/ip/prim/rtl/prim_arbiter.sv
${PRJ_DIR}/hw/ip/prim/rtl/prim_flop_2sync.sv
${PRJ_DIR}/hw/ip/prim/rtl/prim_fifo_sync.sv
${PRJ_DIR}/hw/ip/prim/rtl/prim_subreg.sv
${PRJ_DIR}/hw/ip/prim/rtl/prim_subreg_ext.sv

// TL RTL packages
${PRJ_DIR}/hw/top_earlgrey/rtl/top_pkg.sv
${PRJ_DIR}/hw/ip/tlul/rtl/tlul_pkg.sv
${PRJ_DIR}/hw/ip/tlul/rtl/tlul_assert.sv

// Core RTL
+incdir+${PRJ_DIR}/hw/vendor/lowrisc_ibex/rtl
${PRJ_DIR}/hw/vendor/lowrisc_ibex/rtl/ibex_pkg.sv
${PRJ_DIR}/hw/vendor/lowrisc_ibex/rtl/ibex_tracer_pkg.sv

${PRJ_DIR}/hw/vendor/lowrisc_ibex/rtl/ibex_alu.sv
${PRJ_DIR}/hw/vendor/lowrisc_ibex/rtl/ibex_tracer.sv
${PRJ_DIR}/hw/vendor/lowrisc_ibex/rtl/ibex_compressed_decoder.sv
${PRJ_DIR}/hw/vendor/lowrisc_ibex/rtl/ibex_controller.sv
${PRJ_DIR}/hw/vendor/lowrisc_ibex/rtl/ibex_cs_registers.sv
${PRJ_DIR}/hw/vendor/lowrisc_ibex/rtl/ibex_decoder.sv
${PRJ_DIR}/hw/vendor/lowrisc_ibex/rtl/ibex_ex_block.sv
${PRJ_DIR}/hw/vendor/lowrisc_ibex/rtl/ibex_id_stage.sv
${PRJ_DIR}/hw/vendor/lowrisc_ibex/rtl/ibex_if_stage.sv
${PRJ_DIR}/hw/vendor/lowrisc_ibex/rtl/ibex_load_store_unit.sv
${PRJ_DIR}/hw/vendor/lowrisc_ibex/rtl/ibex_multdiv_slow.sv
${PRJ_DIR}/hw/vendor/lowrisc_ibex/rtl/ibex_multdiv_fast.sv
${PRJ_DIR}/hw/vendor/lowrisc_ibex/rtl/ibex_prefetch_buffer.sv
${PRJ_DIR}/hw/vendor/lowrisc_ibex/rtl/ibex_fetch_fifo.sv
${PRJ_DIR}/hw/vendor/lowrisc_ibex/rtl/ibex_register_file_ff.sv
${PRJ_DIR}/hw/vendor/lowrisc_ibex/rtl/ibex_core.sv
${PRJ_DIR}/hw/ip/rv_core_ibex/rtl/rv_core_ibex.sv

// Core DV files
+incdir+${PRJ_DIR}/hw/ip/rv_core_ibex/dv/env
+incdir+${PRJ_DIR}/hw/ip/rv_core_ibex/dv/tests
+incdir+${PRJ_DIR}/hw/dv/sv/agent/tl_agent
+incdir+${PRJ_DIR}/hw/dv/sv/mem_model
+incdir+${PRJ_DIR}/hw/dv/sv/utils
${PRJ_DIR}/hw/dv/sv/utils/clk_if.sv
${PRJ_DIR}/hw/dv/sv/utils/pins_if.sv
${PRJ_DIR}/hw/dv/sv/utils/dv_utils_pkg.sv
${PRJ_DIR}/hw/dv/sv/mem_model/mem_model_pkg.sv
${PRJ_DIR}/hw/dv/sv/agent/tl_agent/tl_agent_pkg.sv
${PRJ_DIR}/hw/ip/rv_core_ibex/dv/env/core_ibex_env_pkg.sv
${PRJ_DIR}/hw/ip/rv_core_ibex/dv/tests/core_ibex_test_pkg.sv
${PRJ_DIR}/hw/ip/rv_core_ibex/dv/tb/core_ibex_tb_top.sv
${PRJ_DIR}/hw/ip/rv_core_ibex/dv/tb/core_ibex_bind.sv
