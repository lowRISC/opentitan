class i2c_target_stress_wr_vseq extends i2c_target_smoke_vseq;
  `uvm_object_utils(i2c_target_stress_wr_vseq)
  `uvm_object_new

  virtual task body();
     num_trans = 1;
     cfg.min_data = 80;
     cfg.max_data = 80;
     cfg.rs_pct = 0;
     cfg.m_i2c_agent_cfg.use_seq_term = 1;
     
     super.body();     
  endtask // body

   // slow acq fifo read to create acq_fifo full
   task process_acq();
    uvm_reg_data_t read_data;
    i2c_item obs;
    bit is_read;
    bit acq_fifo_empty = 1;      
    int delay;
      
      wait(cfg.sent_acq_cnt > 0);

      
    while (cfg.sent_acq_cnt != cfg.rcvd_acq_cnt ||
	   acq_fifo_empty == 0) begin

       delay = $urandom_range(50, 100);

       // Assuming interval between each byte is 6.2us
       #(delay * 1us);
       
      // polling status.acqempty == 0       
      csr_rd(.ptr(ral.status.acqempty), .value(read_data));
      acq_fifo_empty = read_data;
       
      if (read_data == 0) begin

        // read one entry and compare
        csr_rd(.ptr(ral.acqdata), .value(read_data));
        `uvm_info("process_acq", $sformatf("acq data %x", read_data), UVM_MEDIUM)
        `uvm_create_obj(i2c_item, obs);
        obs = acq2item(read_data);
        is_read = obs.read;

        obs.tran_id = cfg.rcvd_acq_cnt++;
        p_sequencer.target_mode_wr_obs_port.write(obs);
      end else begin // if (read_data == 0)
        cfg.clk_rst_vif.wait_clks(1);
        `uvm_info("process_acq", $sformatf("acq_dbg: sent:%0d rcvd:%0d acq_is_empty",
                                           cfg.sent_acq_cnt, cfg.rcvd_acq_cnt), UVM_HIGH)
      end
    end // while (cfg.sent_acq_cnt != cfg.rcvd_acq_cnt ||...
      cfg.m_i2c_agent_cfg.use_seq_term = 0;
      `JDBG(("assa out"))
   endtask
endclass
