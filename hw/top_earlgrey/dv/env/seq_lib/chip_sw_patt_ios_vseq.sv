// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_patt_ios_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_patt_ios_vseq)
  `uvm_object_new

  typedef struct packed {
    // polarity:
    //    0 : sample rising edge
    //    1 : sample falling edge
    bit          polarity;
    bit [31:0]   clk_div;
    bit [31:0]   patt_lower;
    bit [31:0]   patt_upper;
    // range has +1 value of register
    // to match dif implementation

    // range : [1:64]
    bit [7:0]    len;
    // range : [1, 1024]
    bit [15:0]   rep;
  } pattgen_chan_cfg_t;

  // expected channel config
  pattgen_chan_cfg_t exp_cfg[NUM_PATTGEN_CH];

  // expected 64bit pattern
  bit [63:0]     exp_pat[NUM_PATTGEN_CH];

  rand pattgen_chan_cfg_t rand_chan_cfg;
  rand bit[1:0] chan_en;

  constraint chan_cfg_c {
    // Cover limited sets of divisor in full chip test.
    rand_chan_cfg.clk_div dist { 0 := 4, [1:15] := 1};
    rand_chan_cfg.len inside {[1:64]};
    rand_chan_cfg.rep inside {[1:5]};
  }

  constraint chan_en_c {
    // At least one channel should be enabled.
    chan_en != 2'b0;
  }

  virtual task cpu_init();
    bit[7:0] byte_arr[];
    super.cpu_init();

    cfg.m_pattgen_agent_cfg.en_monitor = 0;

    byte_arr = {chan_en};
    sw_symbol_backdoor_overwrite("kChannelEnable", byte_arr);
    `uvm_info(`gfn, $sformatf("PATT_IOS CHAN_EN: %2b", chan_en), UVM_MEDIUM)

    for (int i = 0; i < NUM_PATTGEN_CH; i++) begin
      exp_cfg[i] = rand_chan_cfg;
      cfg.m_pattgen_agent_cfg.polarity[i] = exp_cfg[i].polarity;
      cfg.m_pattgen_agent_cfg.length[i] = exp_cfg[i].len * exp_cfg[i].rep;
      cfg.m_pattgen_agent_cfg.div[i] = 2 * (exp_cfg[i].clk_div + 1);
      exp_pat[i] = {exp_cfg[i].patt_upper, exp_cfg[i].patt_lower};
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rand_chan_cfg)
    end


    byte_arr = {exp_cfg[0].polarity};
    sw_symbol_backdoor_overwrite("kPattPol0", byte_arr);
    byte_arr = {<<8{{<<32{exp_cfg[0].clk_div}}}};
    sw_symbol_backdoor_overwrite("kPattDiv0", byte_arr);
    byte_arr = {<<8{{<<32{exp_cfg[0].patt_lower}}}};
    sw_symbol_backdoor_overwrite("kPattLower0", byte_arr);
    byte_arr = {<<8{{<<32{exp_cfg[0].patt_upper}}}};
    sw_symbol_backdoor_overwrite("kPattUpper0", byte_arr);
    byte_arr = {exp_cfg[0].len};
    sw_symbol_backdoor_overwrite("kPattLen0", byte_arr);
    byte_arr = {<<8{{<<16{exp_cfg[0].rep}}}};
    sw_symbol_backdoor_overwrite("kPattRep0", byte_arr);

    if (chan_en[0]) begin
      `uvm_info(`gfn, $sformatf("PATT_IOS CH0: cfg %p", exp_cfg[0]), UVM_MEDIUM)
    end

    byte_arr = {exp_cfg[1].polarity};
    sw_symbol_backdoor_overwrite("kPattPol1", byte_arr);
    byte_arr = {<<8{{<<32{exp_cfg[1].clk_div}}}};
    sw_symbol_backdoor_overwrite("kPattDiv1", byte_arr);
    byte_arr = {<<8{{<<32{exp_cfg[1].patt_lower}}}};
    sw_symbol_backdoor_overwrite("kPattLower1", byte_arr);
    byte_arr = {<<8{{<<32{exp_cfg[1].patt_upper}}}};
    sw_symbol_backdoor_overwrite("kPattUpper1", byte_arr);
    byte_arr = {exp_cfg[1].len};
    sw_symbol_backdoor_overwrite("kPattLen1", byte_arr);
    byte_arr = {<<8{{<<16{exp_cfg[1].rep}}}};
    sw_symbol_backdoor_overwrite("kPattRep1", byte_arr);
    if (chan_en[1]) begin
      `uvm_info(`gfn, $sformatf("PATT_IOS CH1: cfg %p", exp_cfg[1]), UVM_MEDIUM)
    end
  endtask // cpu_init

  virtual task body();
    super.body();
    `uvm_info(`gfn, $sformatf("TEST: wait for pinmux init"), UVM_MEDIUM)
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "pinmux_init end")
    `uvm_info(`gfn, $sformatf("TEST: pattgen if enable"), UVM_MEDIUM)
    cfg.chip_vif.enable_pattgen(.enable(1));

    // Avoid false trigger when pad is enabled
    @(cfg.m_pattgen_agent_cfg.vif.pcl_tx);
    // Pattgen needs div4 scale
    cfg.clk_rst_vif.wait_clks(40);
    cfg.m_pattgen_agent_cfg.en_monitor = 1;
    cfg.m_pattgen_agent_cfg.chk_prediv = chan_en;

    fork
      begin
        `DV_WAIT(cfg.sw_logger_vif.printed_log == "TEST DONE")
        cfg.m_pattgen_agent_cfg.channel_done = chan_en;
      end
      collect_pattgen_data();
    join_any

    `uvm_info(`gfn, "TEST: body done", UVM_HIGH)
  endtask

  virtual task collect_pattgen_data();
    foreach (p_sequencer.pattgen_rx_fifo[i]) begin
      automatic int j = i;
      fork begin
        forever process_pattgen_data(j);
      end join_none
    end
  endtask

  // Collect pattgen_item from pattgen agent and check with expected pattern.
  // expected channel config length 'exp_cfg[].len' and repeat value 'exp_cfg[].rep' are used
  // to compare proper size of pattern.
  virtual task process_pattgen_data(int channel);
    pattgen_item item;
    int iter;

    p_sequencer.pattgen_rx_fifo[channel].get(item);

    `uvm_info(`gfn, $sformatf("PATTGEN_CH%0d: got pktlen:%0d",
                              channel, item.data_q.size()), UVM_LOW)
    repeat (exp_cfg[channel].rep) begin
      int bit_cnt = 0;
      while (bit_cnt < exp_cfg[channel].len) begin
        `DV_CHECK_EQ(item.data_q[bit_cnt], exp_pat[channel][bit_cnt],
                     $sformatf("Rep %0d bit_cnt:%0d mismatch", iter, bit_cnt))
        bit_cnt++;
      end
      iter++;
    end
  endtask
endclass // chip_sw_patt_ios_vseq
