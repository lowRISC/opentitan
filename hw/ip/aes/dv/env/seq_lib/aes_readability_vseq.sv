// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test verifies the behavior of different registers matches the specification. In particular:
// - Initial key registers are not readable.
// - Registers are cleared with psuedo-random data if requested (including the unreadable key
//   registers).

class aes_readability_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_readability_vseq)
  `uvm_object_new

  aes_seq_item data_item;
  aes_seq_item cfg_item;
  aes_message_item my_message;
  string str = "";
  int success = 1;

  task body();
    aes_seq_item cfg_item       = new();         // the configuration for this message
    aes_seq_item data_item      = new();
    aes_message_item my_message = new();
    aes_seq_item check_item     = new();

    `uvm_info(`gfn, $sformatf("\n\n\t ----| STARTING AES MAIN SEQUENCE |----\n %s",
                              cfg.convert2string()), UVM_LOW)

    // turnoff keymask
    cfg.key_mask = 0;
    // make sure we write at least a full data word
    cfg.message_len_min = 16;

    // generate list of messages //
    aes_message_init();
    generate_message_queue();

    // check key is unreadable!
    my_message = message_queue.pop_back();
    generate_aes_item_queue(my_message);
    cfg_item   = aes_item_queue.pop_back();
    data_item  = aes_item_queue.pop_back();


    setup_dut(cfg_item);
    foreach (cfg_item.key[0][idx]) begin
      csr_wr(.ptr(ral.key_share0[idx]), .value(cfg_item.key[0][idx]), .blocking(1));
      csr_wr(.ptr(ral.key_share1[idx]), .value(cfg_item.key[1][idx]), .blocking(1));
    end


    foreach (cfg_item.key[0][idx]) begin
      csr_rd(.ptr(ral.key_share0[idx]), .value(check_item.key[0][idx]), .blocking(1));
      csr_rd(.ptr(ral.key_share1[idx]), .value(check_item.key[1][idx]), .blocking(1));
      if ((cfg_item.key[0][idx] == check_item.key[0][idx]) ||
          (cfg_item.key[1][idx] == check_item.key[1][idx])) begin
              `uvm_fatal(`gfn, $sformatf("----| Key reg was Readable |-----"))
      end
    end

    // check read data //
    add_data(data_item.data_in, cfg_item.do_b2b);
    foreach (data_item.data_in[idx]) begin
      csr_rd(.ptr(ral.data_in[idx]), .value(check_item.data_in[idx]), .blocking(1));
      if ( data_item.data_in[idx] == check_item.data_in[idx] ) begin
              `uvm_fatal(`gfn, $sformatf("----|Write data reg was Readable |----"))
      end
    end


    // read output regs before clear
     foreach (data_item.data_out[idx]) begin
      csr_rd(.ptr(ral.data_out[idx]), .value(data_item.data_out[idx]), .blocking(1));
     end
    // read IV before clear
     foreach (data_item.iv[idx]) begin
      csr_rd(.ptr(ral.iv[idx]), .value(data_item.iv[idx]), .blocking(1));
     end


    // clear regs
    clear_regs(2'b11);
    csr_spinwait(.ptr(ral.status.idle) , .exp_data(1'b1));


    success &= uvm_hdl_read("tb.dut.u_reg.hw2reg.data_in[0]", check_item.data_in[0]);
    success &= uvm_hdl_read("tb.dut.u_reg.hw2reg.data_in[1]", check_item.data_in[1]);
    success &= uvm_hdl_read("tb.dut.u_reg.hw2reg.data_in[2]", check_item.data_in[2]);
    success &= uvm_hdl_read("tb.dut.u_reg.hw2reg.data_in[3]", check_item.data_in[3]);

    success &= uvm_hdl_read("tb.dut.u_reg.hw2reg.key_share0[0]", check_item.key[0][0]);
    success &= uvm_hdl_read("tb.dut.u_reg.hw2reg.key_share0[1]", check_item.key[0][1]);
    success &= uvm_hdl_read("tb.dut.u_reg.hw2reg.key_share0[2]", check_item.key[0][2]);
    success &= uvm_hdl_read("tb.dut.u_reg.hw2reg.key_share0[3]", check_item.key[0][3]);
    success &= uvm_hdl_read("tb.dut.u_reg.hw2reg.key_share0[4]", check_item.key[0][4]);
    success &= uvm_hdl_read("tb.dut.u_reg.hw2reg.key_share0[5]", check_item.key[0][5]);
    success &= uvm_hdl_read("tb.dut.u_reg.hw2reg.key_share0[6]", check_item.key[0][6]);
    success &= uvm_hdl_read("tb.dut.u_reg.hw2reg.key_share0[7]", check_item.key[0][7]);

    success &= uvm_hdl_read("tb.dut.u_reg.hw2reg.key_share1[0]", check_item.key[1][0]);
    success &= uvm_hdl_read("tb.dut.u_reg.hw2reg.key_share1[1]", check_item.key[1][1]);
    success &= uvm_hdl_read("tb.dut.u_reg.hw2reg.key_share1[2]", check_item.key[1][2]);
    success &= uvm_hdl_read("tb.dut.u_reg.hw2reg.key_share1[3]", check_item.key[1][3]);
    success &= uvm_hdl_read("tb.dut.u_reg.hw2reg.key_share1[4]", check_item.key[1][4]);
    success &= uvm_hdl_read("tb.dut.u_reg.hw2reg.key_share1[5]", check_item.key[1][5]);
    success &= uvm_hdl_read("tb.dut.u_reg.hw2reg.key_share1[6]", check_item.key[1][6]);
    success &= uvm_hdl_read("tb.dut.u_reg.hw2reg.key_share1[7]", check_item.key[1][7]);
    `DV_CHECK_FATAL(success == 1)


    foreach (data_item.data_in[idx]) begin
      if ((check_item.data_in[idx] == data_item.data_in[idx]) ||
         (check_item.data_out[idx] == data_item.data_out[idx])) begin
        `uvm_fatal(`gfn, $sformatf("----| Data reg was did not clear |---- %s", str))
      end
    end

    foreach (data_item.data_out[idx]) begin
      csr_rd(.ptr(ral.data_out[idx]), .value(check_item.data_out[idx]), .blocking(1));
      if (data_item.data_out[idx] == check_item.data_out[idx] ) begin
        `uvm_fatal(`gfn, $sformatf("----| data out reg was not cleared |---- %s", str))
      end
    end

    // check IV
    foreach (data_item.iv[idx]) begin
      csr_rd(.ptr(ral.iv[idx]), .value(check_item.iv[idx]), .blocking(1));
      if (data_item.iv[idx] == check_item.iv[idx] ) begin
        `uvm_fatal(`gfn, $sformatf("----| IV reg was not cleared |---- %s", str))
      end
    end

    // check key is pseudo random
    foreach (cfg_item.key[0][idx]) begin
      if ((check_item.key[0][idx] == data_item.key[0][idx]) ||
         (check_item.key[1][idx] == data_item.key[1][idx])) begin
        `uvm_fatal(`gfn, $sformatf("----| Key reg was not cleared |---- %s", str))
      end
    end

  endtask // body

endclass // aes_readability_vseq
