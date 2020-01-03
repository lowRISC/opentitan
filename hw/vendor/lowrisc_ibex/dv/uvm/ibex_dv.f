// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

+define+BOOT_ADDR=32'h8000_0000
+define+TRACE_EXECUTION
+define+RVFI

${PRJ_DIR}/ibex/shared/rtl/prim_clock_gating.sv

// ibex CORE RTL files
+incdir+${PRJ_DIR}/ibex/rtl
${PRJ_DIR}/ibex/shared/rtl/prim_assert.sv
${PRJ_DIR}/ibex/rtl/ibex_pkg.sv
${PRJ_DIR}/ibex/rtl/ibex_tracer_pkg.sv
${PRJ_DIR}/ibex/rtl/ibex_tracer.sv
${PRJ_DIR}/ibex/rtl/ibex_alu.sv
${PRJ_DIR}/ibex/rtl/ibex_compressed_decoder.sv
${PRJ_DIR}/ibex/rtl/ibex_controller.sv
${PRJ_DIR}/ibex/rtl/ibex_cs_registers.sv
${PRJ_DIR}/ibex/rtl/ibex_decoder.sv
${PRJ_DIR}/ibex/rtl/ibex_ex_block.sv
${PRJ_DIR}/ibex/rtl/ibex_id_stage.sv
${PRJ_DIR}/ibex/rtl/ibex_if_stage.sv
${PRJ_DIR}/ibex/rtl/ibex_load_store_unit.sv
${PRJ_DIR}/ibex/rtl/ibex_multdiv_slow.sv
${PRJ_DIR}/ibex/rtl/ibex_multdiv_fast.sv
${PRJ_DIR}/ibex/rtl/ibex_prefetch_buffer.sv
${PRJ_DIR}/ibex/rtl/ibex_fetch_fifo.sv
${PRJ_DIR}/ibex/rtl/ibex_register_file_ff.sv
${PRJ_DIR}/ibex/rtl/ibex_core.sv
${PRJ_DIR}/ibex/rtl/ibex_core_tracing.sv

// Core DV files
${PRJ_DIR}/ibex/vendor/google_riscv-dv/src/riscv_signature_pkg.sv
+incdir+${PRJ_DIR}/ibex/dv/uvm/env
+incdir+${PRJ_DIR}/ibex/dv/uvm/tests
+incdir+${PRJ_DIR}/ibex/dv/uvm/common/ibex_mem_intf_agent
+incdir+${PRJ_DIR}/ibex/dv/uvm/common/irq_agent
+incdir+${PRJ_DIR}/ibex/dv/uvm/common/mem_model
+incdir+${PRJ_DIR}/ibex/dv/uvm/common/utils
${PRJ_DIR}/ibex/dv/uvm/common/utils/clk_if.sv
${PRJ_DIR}/ibex/dv/uvm/common/utils/dv_utils_pkg.sv
${PRJ_DIR}/ibex/dv/uvm/common/mem_model/mem_model_pkg.sv
${PRJ_DIR}/ibex/dv/uvm/common/ibex_mem_intf_agent/ibex_mem_intf_agent_pkg.sv
${PRJ_DIR}/ibex/dv/uvm/common/irq_agent/irq_agent_pkg.sv
${PRJ_DIR}/ibex/dv/uvm/env/core_ibex_env_pkg.sv
${PRJ_DIR}/ibex/dv/uvm/tests/core_ibex_test_pkg.sv
${PRJ_DIR}/ibex/dv/uvm/tb/core_ibex_tb_top.sv
