// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rram_ctrl_base_vseq extends cip_base_vseq #(
    .RAL_T               (rram_ctrl_core_reg_block),
    .CFG_T               (rram_ctrl_env_cfg),
    .COV_T               (rram_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T (rram_ctrl_virtual_sequencer)
  );
  `uvm_object_utils(rram_ctrl_base_vseq)

  rram_macro_prim_reg_block prim_ral;

  // Various knobs to enable certain routines
  bit do_rram_ctrl_init = 1'b1;

  uint write_timeout_ns = 1_000_000;  // 1ms

  // Standard SV/UVM methods
  extern function new(string name="");

  // Class specific methods
  extern function void set_handles();
  extern task dut_init(string reset_kind = "HARD");
  extern task rram_ctrl_init();
  extern task rram_ctrl_write(rram_ctrl_op_t rram_ctrl_op, data_q_t data);
  extern task rram_ctrl_read(rram_ctrl_op_t rram_ctrl_op, ref data_q_t data);
  extern task rram_ctrl_wait_op_done();
  extern task rram_host_read(input  addr_t addr,
                             input  bit blocking,
                             input  bit check_rdata,
                             input  data_t exp_rdata,
                             input  prim_mubi_pkg::mubi4_t instr_type,
                             output data_t rdata,
                             output bit completed,
                             input  bit exp_err_rsp
                            );

endclass : rram_ctrl_base_vseq


function rram_ctrl_base_vseq::new(string name="");
  super.new(name);
endfunction : new

function void rram_ctrl_base_vseq::set_handles();
  super.set_handles();
  `downcast(prim_ral, cfg.ral_models[cfg.prim_ral_name]);
endfunction : set_handles

task rram_ctrl_base_vseq::dut_init(string reset_kind = "HARD");
  // Initialize some of DUT inputs
  // TODO
  // cfg.misc_vif.<my_function/my_task>

  super.dut_init();

  if (do_rram_ctrl_init) begin
    rram_ctrl_init();
  end
endtask : dut_init

task rram_ctrl_base_vseq::rram_ctrl_init();
  // TODO
  #1ms;
endtask : rram_ctrl_init

task rram_ctrl_base_vseq::rram_ctrl_wait_op_done();
  uvm_reg_data_t reg_data;
  bit op_start;

  do begin // poll op_done
    csr_rd(.ptr(ral.control), .value(reg_data));
    op_start = get_field_val(ral.control.start, reg_data);
  end while (op_start == 1'b1);
endtask : rram_ctrl_wait_op_done

task rram_ctrl_base_vseq::rram_ctrl_write(rram_ctrl_op_t rram_ctrl_op, data_q_t data);
  uvm_reg_data_t reg_data;
  int            wr_fifo_level;

  // write start address
  csr_wr(.ptr(ral.addr), .value(rram_ctrl_op.addr));

  // write command register
  reg_data = '0;
  reg_data = get_csr_val_with_updated_field(ral.control.start, reg_data, 1'b1);
  reg_data = get_csr_val_with_updated_field(ral.control.op, reg_data, rram_ctrl_op.op);
  reg_data = get_csr_val_with_updated_field(ral.control.partition_sel, reg_data, rram_ctrl_op.partition);
  reg_data = get_csr_val_with_updated_field(ral.control.num, reg_data, rram_ctrl_op.num_words);
  csr_wr(.ptr(ral.control), .value(reg_data));

  // fill wr-fifo
  wr_fifo_level = 0;
  for (int i = 0; i <= rram_ctrl_op.num_words; i++) begin
    if (wr_fifo_level == WrFifoDepth - 1) begin
      do begin // poll fifo until there is space available
        csr_rd(.ptr(ral.curr_fifo_lvl), .value(reg_data));
        wr_fifo_level = get_field_val(ral.curr_fifo_lvl.wr, reg_data);
      end while (wr_fifo_level == WrFifoDepth - 1);
    end
    mem_wr(.ptr(ral.wr_fifo), .offset(0), .data(data[i]));
    wr_fifo_level++;
  end
  // wait for command to complete
  rram_ctrl_wait_op_done();
endtask : rram_ctrl_write

task rram_ctrl_base_vseq::rram_ctrl_read(rram_ctrl_op_t rram_ctrl_op, ref data_q_t data);

  uvm_reg_data_t reg_data;
  int            rd_fifo_level;

  // write start address
  csr_wr(.ptr(ral.addr), .value(rram_ctrl_op.addr));

  // write command register
  reg_data = '0;
  reg_data = get_csr_val_with_updated_field(ral.control.start, reg_data, 1'b1);
  reg_data = get_csr_val_with_updated_field(ral.control.op, reg_data, rram_ctrl_op.op);
  reg_data = get_csr_val_with_updated_field(ral.control.partition_sel, reg_data, rram_ctrl_op.partition);
  reg_data = get_csr_val_with_updated_field(ral.control.num, reg_data, rram_ctrl_op.num_words);
  csr_wr(.ptr(ral.control), .value(reg_data));

  // wait for fifo to be filled and read out
  rd_fifo_level = 0;
  for (int i = 0; i <= rram_ctrl_op.num_words; i++) begin
    if (rd_fifo_level == 0) begin
      do begin
        csr_rd(.ptr(ral.curr_fifo_lvl), .value(reg_data));
        rd_fifo_level = get_field_val(ral.curr_fifo_lvl.rd, reg_data);
      end while (rd_fifo_level == 0);
    end
    mem_rd(.ptr(ral.rd_fifo), .offset(0), .data(data[i]));
    rd_fifo_level--;
  end
  // wait for command to complete
  rram_ctrl_wait_op_done();

endtask : rram_ctrl_read

// Task to perform a direct RRAM read at the specified location:
// Timeout is used to match the longest waiting timeout possible for the host, which will happen
// when the host is waiting for the controller to finish a write operation
task rram_ctrl_base_vseq::rram_host_read(
    input  addr_t addr,
    input  bit blocking = $urandom_range(0, 1),
    input  bit check_rdata = 0,
    input  data_t exp_rdata = '0,
    input  prim_mubi_pkg::mubi4_t instr_type = prim_mubi_pkg::MuBi4False,
    output data_t rdata,
    output bit completed,
    input  bit exp_err_rsp = 1'b0);
  bit         saw_err;
  tl_access_w_abort(.addr(addr), .write(1'b0), .completed(completed), .saw_err(saw_err),
                    .tl_access_timeout_ns(write_timeout_ns), .mask('1),
                    .data(rdata), .exp_err_rsp(exp_err_rsp),
                    .check_exp_data(check_rdata), .exp_data(exp_rdata),
                    .compare_mask('1), .blocking(blocking), .instr_type(instr_type),
                    .tl_sequencer_h(p_sequencer.tl_sequencer_hs[cfg.host_ral_name]));
endtask : rram_read
