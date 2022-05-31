typedef enum bit [1:0] {
    SingleRun, // Singl iteration
    InfiniteRuns, // Run forever until stop is specified
    MultipleRuns, // Multiple runs with configurable or randomizable iteration count
    InvalidRuns // Default state
  } run_type_e;

typedef enum bit [1:0] {
  IsideErr, // Inject error in instruction side memory.
  DsideErr, // Inject error in data side memory.
  PickErr // Pick which memory to inject error in.
  } error_type_e;

class core_base_new_seq #(type REQ = uvm_sequence_item) extends uvm_sequence #(REQ);
  // Default set to 50% for zero delay to be picked. Set to 100 if zero delay is required always.
  int unsigned                     zero_delay_pct = 50;
  rand bit                         zero_delays;
  rand int                         delay = 0;
  int unsigned                     iteration_cnt = 0;
  int unsigned                     max_delay = 500;
  virtual clk_rst_if               clk_vif;
  bit                              stop_seq;
  bit                              seq_finished;
  rand run_type_e                  num_of_iterations = InvalidRuns;
  virtual core_ibex_dut_probe_if   dut_vif;
  // Use this bit to start any unique sequence once
  bit                              start_seq = 0;

  `uvm_object_param_utils(core_base_new_seq#(REQ))

  function new (string name = "");
    super.new(name);
    if(!uvm_config_db#(virtual clk_rst_if)::get(null, "", "clk_if", clk_vif)) begin
       `uvm_fatal(get_full_name(), "Cannot get clk_if")
    end
    if (!uvm_config_db#(virtual core_ibex_dut_probe_if)::get(null, "", "dut_if", dut_vif)) begin
      `uvm_fatal(get_full_name(), "Cannot get dut_if")
    end
  endfunction

  constraint zero_delays_c {
    zero_delays dist {1 :/ zero_delay_pct,
                      0 :/ 100 - zero_delay_pct};
  }
  constraint reasonable_delay_c {
    delay inside {[0 : max_delay]};
  }

  virtual task body();
    if(num_of_iterations == InvalidRuns) begin
      `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(num_of_iterations, num_of_iterations != InvalidRuns;)
    end
    `uvm_info(`gfn, $sformatf("Doing %s", num_of_iterations.name()), UVM_LOW)
    case (num_of_iterations)
      SingleRun: begin
        drive_stimulus(delay);
      end
      MultipleRuns: begin
        if(iteration_cnt == 0) begin
          `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(iteration_cnt,
                                                iteration_cnt > 0 && iteration_cnt <= 20; )
        end
        for (int i = 0; i <= iteration_cnt; i++) begin
          drive_stimulus(delay);
        end
      end
      InfiniteRuns: begin
        while (!stop_seq) begin
          drive_stimulus(delay);
        end
        seq_finished = 1'b1;
      end
      default: begin
        `uvm_fatal(`gfn, "Type of run not set")
      end
    endcase
  endtask: body

  task drive_stimulus(int unsigned delay);
    if(delay == 0) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(zero_delays)
      if(zero_delays) begin
        delay = 0;
      end else begin
        `DV_CHECK_MEMBER_RANDOMIZE_FATAL(delay)
      end
    end
    clk_vif.wait_clks(delay);
    `uvm_info(get_full_name(), "Starting sequence...", UVM_MEDIUM)
    send_req();
    `uvm_info(get_full_name(), "Exiting sequence", UVM_MEDIUM)
  endtask: drive_stimulus

  virtual task send_req();
    `uvm_fatal(get_full_name(), "This task must be implemented in the extended class")
  endtask

  virtual task stop();
    stop_seq = 1'b1;
    `uvm_info(get_full_name(), "Stopping sequence", UVM_MEDIUM)
    wait (seq_finished == 1'b1);
  endtask

endclass

class irq_new_seq extends core_base_new_seq #(irq_seq_item);

  `uvm_object_utils(irq_new_seq)
  `uvm_object_new

  bit no_nmi;
  bit no_fast;
  bit no_external;
  bit no_timer;
  bit no_software;
  int max_delay = 500;
  int min_delay = 50;

  rand int interval = min_delay;

  constraint reasonable_interval_c {
    interval inside {[min_delay : max_delay]};
  }

  virtual task send_req();
    irq_seq_item irq;
    irq = irq_seq_item::type_id::create("irq");
    // Raise interrupts
    start_item(irq);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(irq, num_of_interrupt > 1;
                                        if (no_nmi) {
                                          irq_nm == 0;
                                        }
                                        if (no_fast) {
                                          irq_fast == '0;
                                        }
                                        if (no_external) {
                                          irq_external == 0;
                                        }
                                        if (no_timer) {
                                          irq_timer == 0;
                                        }
                                        if (no_software) {
                                          irq_software == 0;
                                        })
    finish_item(irq);
    get_response(irq);
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(interval)
    clk_vif.wait_clks(interval);
    // Drop interrupts
    start_item(irq);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(irq, num_of_interrupt == 0;)
    finish_item(irq);
    get_response(irq);
  endtask: send_req

endclass: irq_new_seq

// Simple debug sequence
// debug_req is just a single bit sideband signal, use the interface to drive it directly
class debug_new_seq extends core_base_new_seq#(irq_seq_item);

  `uvm_object_utils(debug_new_seq)
  `uvm_object_new

  int max_delay = 500;
  int min_delay = 75;
  rand int unsigned drop_delay = 0;

  virtual task body();
    dut_vif.dut_cb.debug_req <= 1'b0;
    if(drop_delay == 0) begin
      `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(drop_delay,
                                            drop_delay inside {[min_delay : max_delay]};)
    end
    super.body();
  endtask

  virtual task send_req();
    `uvm_info(get_full_name(), "Sending debug request", UVM_HIGH)
    dut_vif.dut_cb.debug_req <= 1'b1;
    clk_vif.wait_clks(drop_delay);
    dut_vif.dut_cb.debug_req <= 1'b0;
  endtask

endclass

class memory_error_seq extends core_base_new_seq#(irq_seq_item);
  core_ibex_vseq               vseq;
  rand error_type_e            err_type = PickErr;
  rand bit                     choose_side;

  `uvm_object_utils(memory_error_seq)
  `uvm_declare_p_sequencer(core_ibex_vseqr)

  function new (string name = "");
    super.new(name);
    vseq = core_ibex_vseq::type_id::create("vseq");
  endfunction

  virtual task send_req();
    case (err_type)
      IsideErr: begin
        vseq.instr_intf_seq.inject_error();
      end
      DsideErr: begin
        vseq.data_intf_seq.inject_error();
      end
      PickErr: begin
        `DV_CHECK_STD_RANDOMIZE_FATAL(choose_side)
        if (choose_side) begin
          vseq.instr_intf_seq.inject_error();
        end else begin
          vseq.data_intf_seq.inject_error();
        end
      end
      default: begin
        // DO nothing
      end
    endcase
    if(!start_seq) begin
      vseq.start(p_sequencer);
      start_seq = 1;
    end
  endtask

endclass: memory_error_seq

class fetch_enable_seq extends core_base_new_seq#(irq_seq_item);

  `uvm_object_utils(fetch_enable_seq)
  `uvm_object_new

  ibex_pkg::fetch_enable_t fetch_enable;
  int unsigned on_bias_pc = 50;
  int max_delay = 500;
  int min_delay = 75;
  rand int unsigned off_delay = 0;

  virtual task body();
    dut_vif.dut_cb.fetch_enable <= ibex_pkg::FetchEnableOn;
    if(off_delay == 0) begin
      `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(off_delay,
                                            off_delay inside {[min_delay : max_delay]};)
    end
    super.body();
  endtask

  virtual task send_req();
    `uvm_info(get_full_name(), "Sending fetch enable request", UVM_LOW)
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(fetch_enable,
                                          fetch_enable dist {ibex_pkg::FetchEnableOn :/ on_bias_pc,
                                                             [0:15] :/ 100 - on_bias_pc};
                                         )
    `uvm_info(`gfn, $sformatf("fetch_enable = %d", fetch_enable), UVM_LOW)
    dut_vif.dut_cb.fetch_enable <= fetch_enable;
    clk_vif.wait_clks(off_delay);
    dut_vif.dut_cb.fetch_enable <= ibex_pkg::FetchEnableOn;

  endtask

endclass
