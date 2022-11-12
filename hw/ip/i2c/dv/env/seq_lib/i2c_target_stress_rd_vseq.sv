class i2c_target_stress_rd_vseq extends i2c_target_smoke_vseq;
  `uvm_object_utils(i2c_target_stress_rd_vseq)
  `uvm_object_new

  virtual task body();
    num_trans = 5;
    cfg.min_data = 100;
    cfg.max_data = 200;
    cfg.wr_pct = 0;
    cfg.rs_pct = 0;
//    cfg.m_i2c_agent_cfg.use_seq_term = 1;

    super.body();
  endtask // body

  task process_txq();
    uvm_reg_data_t data;
    int read_size;
    int rd_txfifo_timeout_ns = 50_000;
     int delay;

    wait(cfg.m_i2c_agent_cfg.sent_byte > 0);

     forever begin
	@(cfg.m_i2c_agent_cfg.vif.cb);
	if (read_rcvd.size() > 0) begin
           read_size = read_rcvd.pop_front();
	end
	delay = $urandom_range(50, 100);
	#(delay * 1us);

      while (read_size > 0) begin
        @(cfg.m_i2c_agent_cfg.vif.cb);

	 if (read_txn_q.size() > 0) begin
          i2c_item item;
          //check tx fifo is full
          csr_spinwait(.ptr(ral.status.txfull), .exp_data(1'b0),
                       .timeout_ns(rd_txfifo_timeout_ns));
          `uvm_create_obj(i2c_item, item)
          item = read_txn_q.pop_front();
          `uvm_info("process_txq", $sformatf("send rdata:%x", item.wdata), UVM_MEDIUM)
          csr_wr(.ptr(ral.txdata), .value(item.wdata));
          read_size--;
        end
      end
     end
  endtask

endclass
