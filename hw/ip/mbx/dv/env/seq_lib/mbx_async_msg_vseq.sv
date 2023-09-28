// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class mbx_async_msg_vseq extends mbx_base_vseq;

  rand uint_t m_req_dw_sz;
  rand uint_t m_rsp_dw_sz;
  rand uint_t m_num_msg;
  rand uint_t m_num_of_iterations;
  rand uint_t m_mbx_num;

  `uvm_object_utils(mbx_async_msg_vseq)

  constraint mbx_num_c { m_mbx_num == 0; }

  constraint req_dw_sz_c { m_req_dw_sz inside {[1 : 5]}; }

  constraint rsp_dw_sz_c { m_rsp_dw_sz inside {[1 : 5]}; }

  constraint num_msg_c { m_num_msg inside {[1 : 2]}; }

  constraint num_of_iterations_c { m_num_of_iterations inside {[1 : 3]}; }

  `uvm_object_new

  virtual task system_thread(uint_t num_msg);
    uint_t msg_rcvd;

    `uvm_info(`gfn,
      $sformatf("system_thread(num_msg=%0d) -- Start", num_msg),
      UVM_DEBUG)
    // Wait for the async msg sts to be set
    csr_spinwait(
      .ptr(m_mbx_soc_ral.m_mbxsoc_reg_block.mbxsts.asyncmsgsts),
      .exp_data(1)
    );
    forever begin
      bit [31:0] rd_data;

      msg_rcvd++;

      // Wait for busy bit to be '0'
      csr_spinwait(
        .ptr(m_mbx_soc_ral.m_mbxsoc_reg_block.mbxsts.mbxbusy),
        .exp_data(0)
      );

      // Generate request
      for(uint_t dw = 0; dw < m_req_dw_sz; dw++) begin
        csr_wr(m_mbx_soc_ral.m_mbxsoc_reg_block.mbxwrdat, $urandom);
      end
      csr_wr(m_mbx_soc_ral.m_mbxsoc_reg_block.mbxctl.mbxgo, 1);

      // Wait for response
      for(uint_t dw = 0; dw < m_rsp_dw_sz; dw++) begin
        csr_spinwait(
          .ptr(m_mbx_soc_ral.m_mbxsoc_reg_block.mbxsts.mbxready),
          .exp_data(1)
        );

         csr_rd(m_mbx_soc_ral.m_mbxsoc_reg_block.mbxrddat, rd_data);
         csr_wr(m_mbx_soc_ral.m_mbxsoc_reg_block.mbxrddat, $urandom);
      end
      // MBXREADY should be '0', once all the data has been read
      csr_rd_check(.ptr(m_mbx_soc_ral.m_mbxsoc_reg_block.mbxsts.mbxready), .compare_value(0));

      // Check if asyncmsgsts is still set
      csr_rd(m_mbx_soc_ral.m_mbxsoc_reg_block.mbxsts.asyncmsgsts, rd_data);

      if(rd_data == 0) begin
        `uvm_info(`gfn, "No more async messages to be sent by core", UVM_LOW)
        break;
      end
      `DV_CHECK_RANDOMIZE_FATAL(this)
    end
    `DV_CHECK_EQ(num_msg, msg_rcvd, "Expected async messages doesn't receive actual")
    `uvm_info(`gfn,
      $sformatf("system_thread(num_msg=%0d) -- End", num_msg),
      UVM_DEBUG)
  endtask: system_thread

  virtual task core_thread(uint_t num_msg);
    `uvm_info(`gfn,
      $sformatf("core_thread(num_msg=%0d) -- Start", num_msg),
      UVM_DEBUG)
    // Set the asyncmsgsts bit
    csr_wr(ral.m_mbxhst_reg_block.mbxsts.asyncmsgsts, 1);

    for(uint_t msg = 0; msg < num_msg; msg++) begin
      byte q[$];

      // Wait for request packet to be written
      wait_for_core_interrupt();

      // Check num of DW sent is same as received
      csr_rd_check(.ptr(ral.m_mbxhst_reg_block.mbxibwrptr),
       .compare_value(m_req_dw_sz * 4 + ral.m_mbxhst_reg_block.mbxibbase.get()));

      // Set MBXIBWRPTR back to MBXIBBASE
      csr_wr(ral.m_mbxhst_reg_block.mbxibwrptr, 0);
      // Clear busy
      csr_wr(ral.m_mbxhst_reg_block.mbxsts.mbxbusy, 0);

      // Create response
      for(uint_t dw = 0; dw < m_rsp_dw_sz; dw++) begin
        for(uint_t byte_cnt = 0; byte_cnt < MBX_DV_DW_SIZE_BYTES; byte_cnt++) begin
          q.push_back($urandom);
        end
      end
      write_mem(obmbx_base_addr, q);
      csr_wr(ral.m_mbxhst_reg_block.mbxobrdptr, 0);
      csr_wr(ral.m_mbxhst_reg_block.mbxobdwcnt, m_rsp_dw_sz);
    end

    // Set asyncmsgsts bit to '0'
    csr_wr(ral.m_mbxhst_reg_block.mbxsts.asyncmsgsts, 0);
    `uvm_info(`gfn,
      $sformatf("core_thread(num_msg=%0d) -- End", num_msg),
      UVM_DEBUG)
  endtask: core_thread

  virtual task body();
    `uvm_info(`gfn, "body -- Start", UVM_DEBUG)
    super.body();
    ibmbx_base_addr.rand_mode(0);
    ibmbx_limit_addr.rand_mode(0);
    obmbx_base_addr.rand_mode(0);
    obmbx_limit_addr.rand_mode(0);
    m_num_of_iterations.rand_mode(0);
    for(uint_t iter = 0; iter < m_num_of_iterations; iter++) begin
      m_num_msg.rand_mode(0);
      fork
        system_thread(m_num_msg);
        core_thread(m_num_msg);
      join
      m_num_msg.rand_mode(1);
      `DV_CHECK_RANDOMIZE_FATAL(this)
    end
    `uvm_info(`gfn, "body -- End", UVM_DEBUG)
  endtask: body

endclass: mbx_async_msg_vseq
