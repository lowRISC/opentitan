// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Basic smoke test vseq
class i2c_target_smoke_vseq extends i2c_base_vseq;
  `uvm_object_utils(i2c_target_smoke_vseq)
  `uvm_object_new

  int tran_id;

  virtual task body();
    i2c_target_base_seq m_i2c_host_seq;
     
    // Intialize dut in device mode and agent in host mode
    initialization(Device);
//    print_time_property();
//    `JDBG(("agtcfg: %s", cfg.m_i2c_agent_cfg.sprint()))

     for (int i = 0; i < 2; i++) begin 
    get_timing_values();
    program_registers();

    `uvm_create_obj(i2c_target_base_seq, m_i2c_host_seq)

     create_write_txn(m_i2c_host_seq);
     m_i2c_host_seq.start(p_sequencer.i2c_sequencer_h);
    `JDBG(("ASSA"))
     end
  endtask : body

   function void print_time_property();
      `JDBG(("timing_prop"))
      `JDBG(("thigh:%0d	     ", thigh));	     // high period of the SCL in clock units
      `JDBG(("tlow:%0d		     ", tlow));		     // low period of the SCL in clock units
      `JDBG(("t_r:%0d		     ", t_r));		     // rise time of both SDA and SCL in clock units
      `JDBG(("t_f:%0d		     ", t_f));		     // fall time of both SDA and SCL in clock units
      `JDBG(("thd_sta:%0d	     ", thd_sta));	     // hold time for (repeated) START in clock units
      `JDBG(("tsu_sta:%0d	     ", tsu_sta));	     // setup time for repeated START in clock units
      `JDBG(("tsu_sto:%0d	     ", tsu_sto));	     // setup time for STOP in clock units
      `JDBG(("tsu_dat:%0d	     ", tsu_dat));	     // data setup time in clock units
      `JDBG(("thd_dat:%0d	     ", thd_dat));	     // data hold time in clock units
      `JDBG(("t_buf:%0d	     ", t_buf));	     // bus free time between STOP and START in clock units
      `JDBG(("t_timeout:%0d	     ", t_timeout));	     // max time target may stretch the clock
      `JDBG(("e_timeout:%0d	     ", e_timeout));	     // max time target may stretch the clock
      `JDBG(("t_sda_unstable:%0d    ", t_sda_unstable));    // sda unstable time during the posedge_clock
      `JDBG(("t_sda_interference:%0d", t_sda_interference)); // sda interference time during the posedge_clock
      `JDBG(("t_scl_interference:%0d", t_scl_interference)); // scl interference time during the posedge_clock

      `JDBG(("error intrs probability"))
      `JDBG(("prob_sda_unstable:%0d    ", prob_sda_unstable));
      `JDBG(("prob_sda_interference:%0d", prob_sda_interference));
      `JDBG(("prob_scl_interference:%0d", prob_scl_interference));
   endfunction // print_timing

   task create_write_txn(ref i2c_target_base_seq seq);
      bit [7:0] wdata_q[$];
      i2c_item txn;
      i2c_item exp_txn;
      
      int txn_size;

      `uvm_create_obj(i2c_item, txn)
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(wdata_q,
				     wdata_q.size() inside {
                                     [cfg.seq_cfg.min_data : cfg.seq_cfg.max_data]};)
      // data + address
      `JDBG(("byte0:0x%x (addr:0x%x) wdataq:%p", {target_addr0, 1'b0}, target_addr0, wdata_q))
      txn_size = wdata_q.size() + 1;

      txn.drv_type = HostStart;
      // skip the first transaction to pass sb because
      // start and address are coalescing in acq fifo.
      seq.req_q.push_back(txn);      
      for (int i = 0; i < txn_size; i++) begin
	 `uvm_create_obj(i2c_item, txn)
	 `uvm_create_obj(i2c_item, exp_txn)
	 txn.drv_type = HostData;
	 txn.stop = 0;	
         txn.tran_id = this.tran_id++; 
	 if (i == 0) begin
	   txn.start = 1;	    
	   txn.wdata[7:1] = target_addr0;
           txn.wdata[0] = 1'b0;
	    
	 end else begin
	   txn.start = 0;	    
	   txn.wdata = wdata_q[i-1];
	 end

	 `downcast(exp_txn, txn.clone());	 
	 seq.req_q.push_back(txn);
	 p_sequencer.target_mode_wr_exp_port.write(exp_txn);	 
      end
      `uvm_create_obj(i2c_item, txn)
      `uvm_create_obj(i2c_item, exp_txn)
      txn.tran_id = this.tran_id++;   
      txn.stop = 1;   
      txn.drv_type = HostStop;
      `downcast(exp_txn, txn.clone());	 
      seq.req_q.push_back(txn);
      p_sequencer.target_mode_wr_exp_port.write(exp_txn);	 
   endtask
endclass : i2c_target_smoke_vseq
