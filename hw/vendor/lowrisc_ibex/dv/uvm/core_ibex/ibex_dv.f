// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Boot address specified in decimal to avoid single quote in number, which
// causes parsing errors of this file in Riviera.
+define+BOOT_ADDR=2147483648 // 32'h8000_0000
+define+TRACE_EXECUTION
+define+RVFI
+incdir+${PRJ_DIR}/ibex/shared/rtl

${PRJ_DIR}/ibex/shared/rtl/prim_clock_gating.sv

// ibex CORE RTL files
+incdir+${PRJ_DIR}/ibex/rtl
${PRJ_DIR}/ibex/shared/rtl/prim_assert.sv
${PRJ_DIR}/ibex/shared/rtl/prim_generic_ram_1p.sv
${PRJ_DIR}/ibex/shared/rtl/prim_secded_28_22_enc.sv
${PRJ_DIR}/ibex/shared/rtl/prim_secded_28_22_dec.sv
${PRJ_DIR}/ibex/shared/rtl/prim_secded_72_64_enc.sv
${PRJ_DIR}/ibex/shared/rtl/prim_secded_72_64_dec.sv
${PRJ_DIR}/ibex/rtl/ibex_pkg.sv
${PRJ_DIR}/ibex/rtl/ibex_tracer_pkg.sv
${PRJ_DIR}/ibex/rtl/ibex_tracer.sv
${PRJ_DIR}/ibex/rtl/ibex_alu.sv
${PRJ_DIR}/ibex/rtl/ibex_compressed_decoder.sv
${PRJ_DIR}/ibex/rtl/ibex_controller.sv
${PRJ_DIR}/ibex/rtl/ibex_cs_registers.sv
${PRJ_DIR}/ibex/rtl/ibex_counters.sv
${PRJ_DIR}/ibex/rtl/ibex_decoder.sv
${PRJ_DIR}/ibex/rtl/ibex_ex_block.sv
${PRJ_DIR}/ibex/rtl/ibex_wb_stage.sv
${PRJ_DIR}/ibex/rtl/ibex_id_stage.sv
${PRJ_DIR}/ibex/rtl/ibex_icache.sv
${PRJ_DIR}/ibex/rtl/ibex_if_stage.sv
${PRJ_DIR}/ibex/rtl/ibex_load_store_unit.sv
${PRJ_DIR}/ibex/rtl/ibex_multdiv_slow.sv
${PRJ_DIR}/ibex/rtl/ibex_multdiv_fast.sv
${PRJ_DIR}/ibex/rtl/ibex_prefetch_buffer.sv
${PRJ_DIR}/ibex/rtl/ibex_fetch_fifo.sv
${PRJ_DIR}/ibex/rtl/ibex_register_file_ff.sv
${PRJ_DIR}/ibex/rtl/ibex_pmp.sv
${PRJ_DIR}/ibex/rtl/ibex_core.sv
${PRJ_DIR}/ibex/rtl/ibex_core_tracing.sv

// Core DV files
${PRJ_DIR}/ibex/vendor/google_riscv-dv/src/riscv_signature_pkg.sv
+incdir+${PRJ_DIR}/ibex/dv/uvm/core_ibex/env
+incdir+${PRJ_DIR}/ibex/dv/uvm/core_ibex/tests
+incdir+${PRJ_DIR}/ibex/dv/uvm/core_ibex/common/ibex_mem_intf_agent
+incdir+${PRJ_DIR}/ibex/dv/uvm/core_ibex/common/irq_agent
+incdir+${PRJ_DIR}/ibex/dv/uvm/core_ibex/common/mem_model
+incdir+${PRJ_DIR}/ibex/dv/uvm/core_ibex/common/utils
${PRJ_DIR}/ibex/dv/uvm/core_ibex/common/utils/clk_if.sv
${PRJ_DIR}/ibex/dv/uvm/core_ibex/common/utils/dv_utils_pkg.sv
${PRJ_DIR}/ibex/dv/uvm/core_ibex/common/mem_model/mem_model_pkg.sv
${PRJ_DIR}/ibex/dv/uvm/core_ibex/common/ibex_mem_intf_agent/ibex_mem_intf.sv
${PRJ_DIR}/ibex/dv/uvm/core_ibex/common/ibex_mem_intf_agent/ibex_mem_intf_agent_pkg.sv
${PRJ_DIR}/ibex/dv/uvm/core_ibex/common/irq_agent/irq_if.sv
${PRJ_DIR}/ibex/dv/uvm/core_ibex/common/irq_agent/irq_agent_pkg.sv
${PRJ_DIR}/ibex/dv/uvm/core_ibex/env/core_ibex_dut_probe_if.sv
${PRJ_DIR}/ibex/dv/uvm/core_ibex/env/core_ibex_rvfi_if.sv
${PRJ_DIR}/ibex/dv/uvm/core_ibex/env/core_ibex_csr_if.sv
${PRJ_DIR}/ibex/dv/uvm/core_ibex/env/core_ibex_env_pkg.sv
${PRJ_DIR}/ibex/dv/uvm/core_ibex/tests/core_ibex_test_pkg.sv
${PRJ_DIR}/ibex/dv/uvm/core_ibex/tb/core_ibex_tb_top.sv
