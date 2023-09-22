// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_scoreboard extends cip_base_scoreboard #(
    .CFG_T(edn_env_cfg),
    .RAL_T(edn_reg_block),
    .COV_T(edn_env_cov)
  );
  `uvm_component_utils(edn_scoreboard)

  virtual edn_cov_if   cov_vif;

  // Specialized `push_pull_item`s
  typedef push_pull_item#(.HostDataWidth(csrng_pkg::CSRNG_CMD_WIDTH)) cs_cmd_item_t;
  typedef push_pull_item#(.HostDataWidth(csrng_pkg::FIPS_GENBITS_BUS_WIDTH)) genbits_item_t;
  typedef push_pull_item#(.HostDataWidth(FIPS_ENDPOINT_BUS_WIDTH)) endpoint_item_t;

  // TLM agent fifos
  uvm_tlm_analysis_fifo#(cs_cmd_item_t) cs_cmd_fifo;
  uvm_tlm_analysis_fifo#(genbits_item_t) genbits_fifo;
  uvm_tlm_analysis_fifo#(endpoint_item_t) endpoint_fifo[MAX_NUM_ENDPOINTS];
  uvm_tlm_analysis_fifo#(bit) rsp_sts_fifo;

  // local queues to hold incoming packets pending comparison
  bit [FIPS_ENDPOINT_BUS_WIDTH - 1:0] endpoint_data_q[$];

  // queues/variables holding commands for comparison at the CSRNG output
  csrng_pkg::csrng_cmd_t sw_cmd_req_q[$];
  csrng_pkg::csrng_cmd_t reseed_cmd_q[$];
  csrng_pkg::csrng_cmd_t generate_cmd_q[$];

  csrng_pkg::csrng_cmd_t sw_cmd_req_comp = edn_reg_pkg::EDN_SW_CMD_REQ_RESVAL;
  csrng_pkg::csrng_cmd_t boot_ins_cmd_comp = edn_reg_pkg::EdnBootInsCmdResval;
  csrng_pkg::csrng_cmd_t boot_gen_cmd_comp = edn_reg_pkg::EdnBootGenCmdResval;
  csrng_pkg::csrng_cmd_t reseed_cmd_comp = edn_reg_pkg::EDN_RESEED_CMD_RESVAL;
  csrng_pkg::csrng_cmd_t generate_cmd_comp = edn_reg_pkg::EDN_GENERATE_CMD_RESVAL;

  // indicator bit, 1'b1 if EDN is in boot mode
  bit boot_mode = 1'b0;
  // indicator bit, 1'b1 if EDN is in auto mode
  bit auto_mode = 1'b0;
  // indicator bit, 1'b1 if EDN was instantiated
  bit instantiated = 1'b0;
  // indicator bit, 1'b1 if in boot_req_mode and generate cmd has been sent
  bit boot_gen_cmd_sent = 1'b0;
  // counter to keep track of additional data
  int clen_cntr = 0;
  // EDN previous and current ctrl state
  edn_reg_pkg::edn_reg2hw_ctrl_reg_t edn_ctrl_pre = edn_reg_pkg::CtrlResval;
  edn_reg_pkg::edn_reg2hw_ctrl_reg_t edn_ctrl = edn_reg_pkg::CtrlResval;
  // MAX_NUM_REQS_BETWEEN_RESEEDS state and ctr
  bit [31:0] max_num_reqs_between_reseeds = edn_reg_pkg::MaxNumReqsBetweenReseedsResval;
  bit [31:0] reqs_between_reseeds_ctr     = edn_reg_pkg::MaxNumReqsBetweenReseedsResval;

  // Sample interrupt pins at read data phase. This is used to compare with intr_state read value.
  bit [NumEdnIntr-1:0] intr_pins;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    genbits_fifo = new("genbits_fifo", this);
    cs_cmd_fifo  = new("cs_cmd_fifo", this);
    rsp_sts_fifo = new("cs_rsp_sts_fifo", this);

    for (int i = 0; i < MAX_NUM_ENDPOINTS; i++) begin
      endpoint_fifo[i] = new($sformatf("endpoint_fifo[%0d]", i), this);
    end

    if (!uvm_config_db#(virtual edn_cov_if)::get(null, "*.env" , "edn_cov_if", cov_vif)) begin
      `uvm_fatal(`gfn, $sformatf("Failed to get edn_cov_if from uvm_config_db"))
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);

    fork
      process_cs_cmd_fifo();
      process_genbits_fifo();
      process_rsp_sts_fifo();
    join_none

    for (int i = 0; i < MAX_NUM_ENDPOINTS; i++) begin
      automatic int j = i;
      fork
        begin
          process_endpoint_fifo(j);
        end
      join_none;
    end
  endtask

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
    bit     do_read_check   = 1'b1;
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);

    bit addr_phase_read   = (!write && channel == AddrChannel);
    bit addr_phase_write  = (write && channel == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);
    bit data_phase_write  = (write && channel == DataChannel);

    // bools to determine whether sm is done and FIFOs need to be reset
    bit auto_req_mode_turned_off;
    bit boot_req_mode_turned_off;
    bit main_sm_done;

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end
    else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    if (csr.get_name() == "ctrl") begin
      edn_ctrl_pre = edn_ctrl;
    end

    // if incoming access is a write to a valid csr, then make updates right away
    if (addr_phase_write) begin
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
    end

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    case (csr.get_name())
      // add individual case item for each csr
      "intr_state": begin
        if (addr_phase_read) intr_pins = cfg.intr_vif.pins;
        if (data_phase_read) begin
          bit [NumEdnIntr-1:0] intr_en = `gmv(ral.intr_enable);
          foreach (intr_pins[i]) begin
            edn_intr_e intr = edn_intr_e'(i);
            `DV_CHECK_CASE_EQ(intr_pins[i], (intr_en[i] & item.d_data[i]),
                              $sformatf("Interrupt_pin: %0s", intr.name));
            if (cfg.en_cov) begin
              cov.intr_cg.sample(i, intr_en[i], item.d_data[i]);
              cov.intr_pins_cg.sample(i, intr_pins[i]);
            end
          end
        end
        do_read_check = 1'b0;
      end
      "intr_enable": begin
        // FIXME
      end
      "intr_test": begin
        if (addr_phase_write && cfg.en_cov) begin
          bit [NumEdnIntr-1:0] intr_en  = `gmv(ral.intr_enable);
          bit [NumEdnIntr-1:0] intr_exp = `gmv(ral.intr_state) | item.a_data;
          foreach (intr_exp[i]) begin
            cov.intr_test_cg.sample(i, item.a_data[i], intr_en[i], intr_exp[i]);
          end
        end
      end
      "ctrl": begin
        // update current ctrl state
        edn_ctrl.edn_enable.q = `gmv(ral.ctrl.edn_enable);
        edn_ctrl.auto_req_mode.q = `gmv(ral.ctrl.auto_req_mode);
        edn_ctrl.boot_req_mode.q = `gmv(ral.ctrl.boot_req_mode);
        edn_ctrl.cmd_fifo_rst.q = `gmv(ral.ctrl.cmd_fifo_rst);

        // reset fifos if cmd_fifo_rst is true
        if (write && (edn_ctrl.cmd_fifo_rst.q == MuBi4True)) begin
          reseed_cmd_q.delete();
          generate_cmd_q.delete();
        end

        if (write && (edn_ctrl.edn_enable.q == MuBi4True)) begin
          // set boot mode flag if boot_req_mode is true and we are not already in auto mode
          // boot mode has priority over auto mode if they are turned on at the same time
          if (edn_ctrl.boot_req_mode.q == MuBi4True && !auto_mode) begin
            boot_mode = 1'b1;
          end
          // set auto mode flag if auto_req_mode is true and we are not already in boot mode
          if (edn_ctrl.auto_req_mode.q == MuBi4True && !boot_mode)  begin
            auto_mode = 1'b1;
          end

          // If EDN was disabled and is now enabled, set the initial state
          if ((edn_ctrl_pre.edn_enable.q != MuBi4True) || (cfg.backdoor_disable)) begin
            clen_cntr = 0;
            reqs_between_reseeds_ctr = 32'b0;
            cfg.backdoor_disable = 1'b0;
            instantiated = 1'b0;
            boot_gen_cmd_sent = 1'b0;
            sw_cmd_req_q.delete();

            // clear auto mode fifos if Main_SM enters SW_Port_Mode
            if (edn_ctrl.boot_req_mode.q != MuBi4True &&
                edn_ctrl.auto_req_mode.q != MuBi4True) begin
              reseed_cmd_q.delete();
              generate_cmd_q.delete();
            end

          // If auto mode is being disabled wait for SM to enter Idle state and clear FIFOs
          end else if ((edn_ctrl.auto_req_mode.q != MuBi4True) &&
                       (edn_ctrl_pre.auto_req_mode.q == MuBi4True)) begin
            fork
              begin
                csr_spinwait(.ptr(ral.main_sm_state), .exp_data(edn_pkg::Idle), .backdoor(1'b1));
                reseed_cmd_q.delete();
                generate_cmd_q.delete();
                auto_mode = 1'b0;
                if (edn_ctrl.boot_req_mode.q == MuBi4True) begin
                  boot_mode = 1'b1;
                end
              end
            join_none
          end
        end

        // currently FIFOs aren't cleared when EDN is disabled.
        // Uncomment based on decision in #19653
        // reseed_cmd_q.delete();
        // generate_cmd_q.delete();

      end
      "sw_cmd_req": begin
        // Only save sw commands if we are in a state that allows for sw commands
        bit sw_cmd_allowed = (boot_mode && boot_gen_cmd_sent) ||
                             (!boot_mode && !auto_mode) ||
                             (auto_mode && !instantiated);

        if (addr_phase_write && `gmv(ral.sw_cmd_sts.cmd_rdy) && sw_cmd_allowed) begin
          sw_cmd_req_q.push_back(item.a_data);
        end
      end
      "sw_cmd_sts": begin
        do_read_check = 1'b0;
      end
      "boot_ins_cmd": begin
        if (addr_phase_write) begin
          boot_ins_cmd_comp = item.a_data;
        end
      end
      "boot_gen_cmd": begin
        if (addr_phase_write) begin
          boot_gen_cmd_comp = item.a_data;
        end
      end
      "sum_sts": begin
      end
      "generate_cmd": begin
        if (addr_phase_write) begin
          generate_cmd_q.push_back(item.a_data);
        end
      end
      "reseed_cmd": begin
        if (addr_phase_write) begin
          reseed_cmd_q.push_back(item.a_data);
        end
      end
      "max_num_reqs_between_reseeds": begin
        if (addr_phase_write) begin
          max_num_reqs_between_reseeds = item.a_data;
          reqs_between_reseeds_ctr = 32'b0;
        end
      end
      "recov_alert_sts": begin
      end
      "alert_test", "err_code", "err_code_test", "regwen": begin
        // Do nothing.
      end
      "main_sm_state": begin
        do_read_check = 1'b0;
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
      end
    endcase

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (data_phase_read) begin
      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                     $sformatf("reg name: %0s", csr.get_full_name()))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask

  task process_cs_cmd_fifo();
    cs_cmd_item_t cs_cmd_item;
    csrng_pkg::csrng_cmd_t cs_cmd;
    csrng_pkg::acmd_e acmd_cur; // store current acmd to determine where additional data comes from

    instantiated = 1'b0;
    clen_cntr = 0;
    reqs_between_reseeds_ctr = 32'b0;

    forever begin
      cs_cmd_fifo.get(cs_cmd_item);
      cs_cmd = cs_cmd_item.h_data[csrng_pkg::CSRNG_CMD_WIDTH-1:0];

      // Check if EDN is disabled
      `DV_CHECK_FATAL((edn_ctrl.edn_enable.q == MuBi4True) && !cfg.backdoor_disable,
                      $sformatf("No commands can be issued if EDN is disabled. cmd: 0x%h", cs_cmd))

      // If cs_cmd contains additional data
      if (clen_cntr != 0) begin
        // Decrease additional data counter
        clen_cntr--;
        // If this is the last word of an instantiate command, set the appropriate flags
        if ((acmd_cur == csrng_pkg::INS) && (clen_cntr == 0)) begin
          instantiated = 1'b1;
        end

        // Determine which fifo to compare the additional data with
        // If the EDN is in boot_req_mode and boot sequence is not done
        // no additional data is allowed
        `DV_CHECK_FATAL(boot_mode -> boot_gen_cmd_sent,
                        $sformatf({"Additional data not allowed in boot_req_mode",
                                   " if boot is not complete. cmd: 0x%h"},
                                  cs_cmd))

        // If the EDN is in auto_req_mode
        // determine whether the additional data comes from a reseed or a generate cmd.
        if (auto_mode) begin
          case (acmd_cur)
            csrng_pkg::INS: begin
              sw_cmd_req_comp = sw_cmd_req_q.pop_front();
              `DV_CHECK_FATAL(cs_cmd == sw_cmd_req_comp,
                              $sformatf({"Additional data 0x%h in auto_req_mode has to match",
                                         " the value from sw_cmd_req register 0x%h."},
                                        cs_cmd, sw_cmd_req_comp))
            end
            csrng_pkg::RES: begin
              reseed_cmd_comp = reseed_cmd_q.pop_front();
              reseed_cmd_q.push_back(reseed_cmd_comp);
              `DV_CHECK_FATAL(cs_cmd == reseed_cmd_comp,
                              $sformatf({"Additional data 0x%h in auto_req_mode has to match",
                                         " the value from reseed fifo 0x%h."},
                                        cs_cmd, reseed_cmd_comp))
            end
            csrng_pkg::GEN: begin
              generate_cmd_comp = generate_cmd_q.pop_front();
              generate_cmd_q.push_back(generate_cmd_comp);
              `DV_CHECK_FATAL(cs_cmd == generate_cmd_comp,
                              $sformatf({"Additional data 0x%h in auto_req_mode has to match",
                                         " the value from generate fifo 0x%h."},
                                        cs_cmd, generate_cmd_comp))
            end
            default: begin
              `uvm_error(`gfn, $sformatf({"Only additional data for reseed and generate accepted",
                                          " in auto_req_mode. cmd: 0x%h"}, cs_cmd))
            end
          endcase
        end

        // If the EDN is in sw mode, the additional data must come from sw_cmd_req
        if (!auto_mode && !boot_mode) begin
          sw_cmd_req_comp = sw_cmd_req_q.pop_front();
          `DV_CHECK_FATAL(cs_cmd == sw_cmd_req_comp,
                          $sformatf({"Additional data 0x%h in sw mode has to match",
                                     " the value from sw fifo 0x%h."},
                                    cs_cmd, sw_cmd_req_comp))
        end

      // Else cs_cmd contains a command header
      end else begin
        clen_cntr = cs_cmd.clen;
        acmd_cur = cs_cmd.acmd;

        case (acmd_cur)
          csrng_pkg::INS: begin
            // Check if already instantiated
            `DV_CHECK_FATAL(!instantiated,
                            $sformatf({"Instantiate command not allowed for instantiated",
                                       " CSRNG instance. the value from generate fifo 0x%h."},
                                      cs_cmd))

            // Determine whether the instantiate only consists of the header
            // and set flags accordingly
            if (clen_cntr == 0) begin
              instantiated = 1'b1;
            end

            // If EDN is in boot_req_mode and boot sequence is not done
            if (boot_mode && (boot_gen_cmd_sent == 1'b0)) begin
              `DV_CHECK_FATAL(cs_cmd == boot_ins_cmd_comp,
                              $sformatf({"Instantiate command 0x%h in boot_req_mode",
                                         " has to match the value in boot_ins_cmd register 0x%h."},
                                        cs_cmd, boot_ins_cmd_comp))

            // If EDN is in auto_req_mode
            end else if (auto_mode) begin
              sw_cmd_req_comp = sw_cmd_req_q.pop_front();
              `DV_CHECK_FATAL(cs_cmd == sw_cmd_req_comp,
                              $sformatf({"Instantiate command 0x%h in auto_req_mode",
                                         " has to match the value in sw_cmd_req register 0x%h."},
                                        cs_cmd, sw_cmd_req_comp))

            // If EDN is in sw mode or boot_gen command has been sent
            end else begin
              sw_cmd_req_comp = sw_cmd_req_q.pop_front();
              `DV_CHECK_FATAL(cs_cmd == sw_cmd_req_comp,
                              $sformatf({"Instantiate command 0x%h in sw mode",
                                         " has to match the value in sw_cmd_req register 0x%h."},
                                        cs_cmd, sw_cmd_req_comp))
            end
          end
          csrng_pkg::RES: begin
            // Check if not instantiated
            `DV_CHECK_FATAL(instantiated,
                            $sformatf({"Reseed command not allowed without instantiated",
                                       " CSRNG instance. cmd: 0x%h"}, cs_cmd))

            // If EDN is in boot_req_mode and boot sequence is not done
            `DV_CHECK_FATAL(boot_mode -> boot_gen_cmd_sent,
                            $sformatf({"Reseed command not allowed in boot_req_mode.",
                                       " cmd: 0x%h"}, cs_cmd))

            // If EDN is in auto_req_mode
            if (auto_mode) begin
              reseed_cmd_comp = reseed_cmd_q.pop_front();
              reseed_cmd_q.push_back(reseed_cmd_comp);
              reqs_between_reseeds_ctr = 32'b0;
              `DV_CHECK_FATAL(cs_cmd == reseed_cmd_comp,
                              $sformatf({"Reseed command 0x%h in auto_req_mode",
                                         " has to match the value in reseed fifo 0x%h."},
                                        cs_cmd, reseed_cmd_comp))

            // If EDN is in sw mode or boot_gen command has been sent
            end else begin
              sw_cmd_req_comp = sw_cmd_req_q.pop_front();
              `DV_CHECK_FATAL(cs_cmd == sw_cmd_req_comp,
                              $sformatf({"Reseed command 0x%h in sw mode",
                                         " has to match the value in sw_cmd_req register 0x%h."},
                                        cs_cmd, sw_cmd_req_comp))
            end
          end
          csrng_pkg::GEN: begin
            // Check if not instantiated
            `DV_CHECK_FATAL(instantiated,
                            $sformatf({"Generate command not allowed without instantiated",
                                       " CSRNG instance. cmd: 0x%h"}, cs_cmd))

            // If EDN is in boot_req_mode and boot sequence is not done
            if (boot_mode && (boot_gen_cmd_sent == 1'b0)) begin
              `DV_CHECK_FATAL(cs_cmd == boot_gen_cmd_comp,
                              $sformatf({"Generate command 0x%h in boot_req_mode",
                                         " has to match the value in boot_gen_cmd register 0x%h."},
                                        cs_cmd, boot_gen_cmd_comp))
              // Once the MAIN_SM enters the boot done state, the FIFOs have to be cleared
              boot_gen_cmd_sent = 1'b1;
              reseed_cmd_q.delete();
              generate_cmd_q.delete();

            // If EDN is in auto_req_mode
            end else if (auto_mode) begin
              generate_cmd_comp = generate_cmd_q.pop_front();
              generate_cmd_q.push_back(generate_cmd_comp);

              `DV_CHECK_FATAL(cs_cmd == generate_cmd_comp,
                              $sformatf({"Generate command 0x%h in auto_req_mode",
                                         " has to match the value in generate fifo 0x%h."},
                                        cs_cmd, generate_cmd_comp))

              `DV_CHECK_FATAL(reqs_between_reseeds_ctr < max_num_reqs_between_reseeds,
                              $sformatf({"Maximum number of request between reseeds",
                                         " in auto_req_mode 0x%h exceeded."},
                                        max_num_reqs_between_reseeds))

              reqs_between_reseeds_ctr++;

            // If EDN is in sw mode or boot_gen command has been sent
            end else begin
              sw_cmd_req_comp = sw_cmd_req_q.pop_front();

              `DV_CHECK_FATAL(cs_cmd == sw_cmd_req_comp,
                              $sformatf({"Generate command 0x%h in sw mode",
                                         " has to match the value in sw_cmd_req register 0x%h."},
                                        cs_cmd, sw_cmd_req_comp))

            end
          end
          csrng_pkg::UPD: begin
            // Check if not instantiated
            `DV_CHECK_FATAL(instantiated,
                            $sformatf({"Update command not allowed without instantiated",
                                       " CSRNG instance. cmd: 0x%h"}, cs_cmd))

            // If EDN is in boot_req_mode and boot sequence is not done
            `DV_CHECK_FATAL(boot_mode -> boot_gen_cmd_sent,
                            $sformatf({"Update command not allowed in boot_req_mode.",
                                       " cmd: 0x%h"}, cs_cmd))

            // If EDN is in auto_req_mode
            `DV_CHECK_FATAL(!auto_mode,
                            $sformatf({"Update command not allowed in auto_req_mode.",
                                       " cmd: 0x%h"}, cs_cmd))

            // If EDN is in sw mode or boot_gen command has been sent
            sw_cmd_req_comp = sw_cmd_req_q.pop_front();
            `DV_CHECK_FATAL(cs_cmd == sw_cmd_req_comp,
                            $sformatf({"Update command 0x%h in sw mode has to match",
                                        " the value from sw_cmd_req register 0x%h."},
                                      cs_cmd, sw_cmd_req_comp))

          end
          csrng_pkg::UNI: begin
            // Check if not instantiated
            `DV_CHECK_FATAL(instantiated,
                            $sformatf({"Uninstantiate command not allowed without instantiated",
                                       " CSRNG instance. cmd: 0x%h"}, cs_cmd))

            `DV_CHECK_FATAL(clen_cntr == 0,
                            $sformatf("clen must be 0 for uninstantiate command. cmd: 0x%h",
                                      cs_cmd))

            if (!auto_mode && !boot_mode) begin
              sw_cmd_req_comp = sw_cmd_req_q.pop_front();
              `DV_CHECK_FATAL(cs_cmd == sw_cmd_req_comp,
                              $sformatf({"Uninstantiate command 0x%h in sw mode has to match",
                                          " the value from sw_cmd_req register 0x%h."},
                                        cs_cmd, sw_cmd_req_comp))
            end
            instantiated = 1'b0;
          end
          default: begin
            `uvm_error(`gfn, $sformatf("Invalid application command. cmd: 0x%h", cs_cmd))
          end
        endcase
      end
    end

  endtask

  task process_genbits_fifo();
    genbits_item_t                  genbits_item;
    bit[ENDPOINT_BUS_WIDTH - 1:0]   endpoint_data;
    bit                             fips;

    forever begin
      genbits_fifo.get(genbits_item);
      fips = genbits_item.h_data[csrng_pkg::GENBITS_BUS_WIDTH];
      for (int i = 0; i < csrng_pkg::GENBITS_BUS_WIDTH/ENDPOINT_BUS_WIDTH; i++) begin
        endpoint_data = genbits_item.h_data >> (i * ENDPOINT_BUS_WIDTH);
        endpoint_data_q.push_back({fips, endpoint_data});
      end
    end
  endtask

  task process_rsp_sts_fifo();
    bit   rsp_sts;

    forever begin
      rsp_sts_fifo.get(rsp_sts);
      if ((cfg.boot_req_mode == MuBi4False) && (cfg.auto_req_mode == MuBi4False)) begin
        // Check register value if not boot_req_mode/auto_req_mode
        csr_spinwait(.ptr(ral.sw_cmd_sts.cmd_sts), .exp_data(rsp_sts));
      end
    end
  endtask

  task process_endpoint_fifo(uint endpoint);
    endpoint_item_t endpoint_item;
    uint   index, q_size;
    bit    match;

    forever begin
      endpoint_fifo[endpoint].get(endpoint_item);
      index = 0;
      match = 0;
      q_size = endpoint_data_q.size();
      do begin
        if (endpoint_item.d_data == endpoint_data_q[index]) begin
          match = 1;
          endpoint_data_q.delete(index);
        end
        else if (index == q_size - 1) begin
          `uvm_fatal(`gfn, $sformatf("No match for endpoint_data: %h", endpoint_item.d_data))
        end
        else begin
          index++;
        end
      end
      while (!match);
    end
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);

    // For queues that have to be empty at the end of each test, check that they are actually empty and print
    // remaining items if they aren't.  For queues that don't have to empty at the end of each test, describe
    // why.

    // TODO(#18857): Uncomment the following line once items from `cs_cmd_fifo` get processed.
    // `DV_EOT_PRINT_TLM_FIFO_CONTENTS(cs_cmd_item_t, cs_cmd_fifo)

    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(genbits_item_t, genbits_fifo)

    `DV_EOT_PRINT_TLM_FIFO_ARR_CONTENTS(endpoint_item_t, endpoint_fifo)

    // `DV_EOT_PRINT_TLM_FIFO_CONTENTS` does not work for items of type `bit`, which don't have a
    // `sprint` method.
    while (!rsp_sts_fifo.is_empty()) begin
      bit item;
      void'(rsp_sts_fifo.try_get(item));
      `dv_error($sformatf("rsp_sts_fifo item uncompared: %0b", item), `gfn)
    end

    // `endpoint_data_q` does not necessarily have to be empty at the end of a test, because it
    // contains entropy flits that have been generated by CSRNG and thus would be valid to deliver
    // to endpoints, but if endpoints don't request *all* entropy generated by CSRNG, some flits
    // will remain in `endpoint_data_q`.
  endfunction

endclass
