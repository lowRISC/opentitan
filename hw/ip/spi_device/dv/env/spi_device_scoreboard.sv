// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_device_scoreboard extends cip_base_scoreboard #(.CFG_T (spi_device_env_cfg),
                                                          .RAL_T (spi_device_reg_block),
                                                          .COV_T (spi_device_env_cov));
  `uvm_component_utils(spi_device_scoreboard)

  localparam int FLASH_STATUS_UPDATE_DLY_AFTER_CSB_DEASSERT = 4;
  typedef enum int {
    NoInternalProcess,
    InternalProcessStatus,
    InternalProcessJedec,
    InternalProcessSfdp,
    InternalProcessReadCmd,
    // cmd like write enable/disable, enter/exit 4B addr
    InternalProcessCfgCmd,
    UploadCmd
  } internal_process_cmd_e;

  // TLM fifos to pick up the packets
  uvm_tlm_analysis_fifo #(spi_item) upstream_spi_host_fifo;
  uvm_tlm_analysis_fifo #(spi_item) upstream_spi_device_fifo;
  // connect with req_analysis_port where it receives item when opcode and address are received
  uvm_tlm_analysis_fifo #(spi_item) upstream_spi_req_fifo;
  uvm_tlm_analysis_fifo #(spi_item) downstream_spi_host_fifo;

  // RX a SPI-txn the when CSB is active
  uvm_tlm_analysis_fifo #(spi_item) upstream_csb_active_fifo;

  // mem model to save expected value
  local mem_model tx_mem;
  local mem_model rx_mem;
  local uint tx_rptr_exp;
  local uint rx_wptr_exp;
  local mem_model spi_mem;

  // when interrupt is triggered, it may take a few cycles before it's reflected in a TL read
  local bit [NumSpiDevIntr-1:0] intr_trigger_pending;
  local bit [NumSpiDevIntr-1:0] intr_exp_read_mirrored;
  //TB will set bits below when the interrupt is on its way to be pending on the predicted side
  local bit [NumSpiDevIntr-1:0] intr_pending_set_after_delay;
  //TB will set bits below when interrupt is on its way to be pending, but the RTL read the bit set before the TB had set it due to the delay
  local bit [NumSpiDevIntr-1:0] intr_pending_read_set_before_delay;

  // tx/rx async fifo, size is 2 words
  local bit [31:0] tx_word_q[$];
  local bit [31:0] rx_word_q[$];

  //Tracks whether there's an ongoing read_buffer_cmd
  bit              ongoing_read_buffer_cmd;
  bit read_pipeline_ongoing_read_buffer_cmd, read_pipeline_read_buffer_cmd_last;
  int unsigned last_readbuf_intr_update_spi_clk_cycle;
  int unsigned last_read_buffer_addr;
  bit          readbuf_int_predicted_already, readwatermark_int_predicted_already;
  // Set to 1 when the last read command has no payload
  bit          last_read_cmd_no_payload;

  // for passthrough
  spi_item spi_passthrough_downstream_q[$];

  // for upload
  bit [7:0] upload_cmd_q[$];
  bit [31:0] upload_addr_q[$];

  // for read buffer
  // once triggered, it won't be triggered again until it flips
  bit read_buffer_watermark_triggered;

  // ADDR_MODE TL side values;
  bit tl_ul_side_addr_mode_pending;
  bit tl_ul_side_addr_mode_addr_4b_en;
  bit spi_side_addr_mode_addr_4b_en;
  event check_addr_mode_propagation_ev;

  // Predicted spi-side flash status
  flash_status_t spi_side_flash_status;
  // flash_status value written on TL-UL. There can be several (RTL supports up to 2) writes on the
  // TL-UL CDC side before it's seen on the SPI CDC side.
  flash_status_t tl_ul_side_flash_status_q[$];
  // Needed for when TL-UL read occurs before CDC transition from SPI->UL after CSB is inactive.
  // It'll have up to 2 items max. That's because once CSB goes high, if SW reads flash_status we
  // may get the "old old" flash_status (no longer the active one, but had already been pushed to
  // the parallel to serial buffer), or the new "old" value depending on when the read arrives
  flash_status_t tl_ul_old_flash_status_q[$];
  // This queue will have 1 entry at most, and it'll be populated whenever SW writes to flash_status
  // Used to store values written not known if yet committed to the TL-UL-side
  flash_status_t tl_ul_fuzzy_flash_status_q[$];
  // This queue will have 1 entry at most, and it'll be populated if there's a SW write used to
  // store values written not known if yet committed to the SPI-side
  flash_status_t spi_side_fuzzy_flash_status_q[$];

  // Triggered after TB updates spi-side status bits from TL-UL to compare READ_STATUS command bits
  event check_spi_status_bits_ev;

  // Triggered after CSB is asserted
  event CSB_not_active_ev;

  // Samples spi-side flash_status.busy at CSB active: The busy bit is latched at CSB deassertion
  bit spi_side_fs_busy_at_csb_low;

  // Set to 1 when there's an ongoing flash READ_STATUS#1/2/3 command
  bit   ongoing_read_status_cmd;
  bit   update_spi_side_flash_status_after_read_status;
  // for TPM mode
  local spi_item tpm_read_sw_q[$];
  // when host reads a TPM HW reg, SW may update its value at the same time
  // it's ok that host reads either the old value or the new one.
  // Store the old value here and clear this array when the SPI transaction is completed
  local bit[TL_DW-1:0] tpm_hw_reg_pre_val_aa[string];

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    upstream_spi_host_fifo = new("upstream_spi_host_fifo", this);
    upstream_spi_device_fifo = new("upstream_spi_device_fifo", this);
    upstream_spi_req_fifo = new("upstream_spi_req_fifo", this);
    downstream_spi_host_fifo = new("downstream_spi_host_fifo", this);
    upstream_csb_active_fifo = new("upstream_csb_active_fifo",this);
    tx_mem = mem_model#()::type_id::create("tx_mem", this);
    rx_mem = mem_model#()::type_id::create("rx_mem", this);

    `DV_CHECK_FATAL(exp_mem.exists(RAL_T::type_name))
    spi_mem = exp_mem[RAL_T::type_name];
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    if (cfg.en_scb) fork
      process_upstream_spi_host_fifo();
      process_upstream_spi_device_fifo();
      process_downstream_spi_fifo();
      upstream_req_fifo_distributor();
      process_tl2spi_updates();
      process_clear_mems();
      check_addr_mode_propagation();
    join_none
  endtask

  // reinitialises memory models when cfg.scb_clear_mems is asserted.
  task process_clear_mems();
    forever begin
      wait(cfg.scb_clear_mems);
      clear_mems();
      cfg.scb_clear_mems = 0;
    end
  endtask : process_clear_mems

  // extract spi items sent from host
  virtual task process_upstream_spi_host_fifo();
    spi_item item;
    forever begin
      bit is_status, is_jedec, is_sfdp, is_mbx_read;
      bit update_wel, wel_val;
      // Note: depending on the timing of flash_status writes, some WREN/WRDI commands may be
      // 'suppressed' by the flash_status write. For example, if a write was clearing WEL, whilst
      // there is a flash WREN command the TB doesn't know the write value will go through CDC. So,
      // TB just reads RTL's committed value to know if the write crossed CDCs before/after flash
      // command
      uvm_hdl_data_t rtl_sck_committed_status;
      flash_status_t rtl_committed_flash_status;

      upstream_spi_host_fifo.get(item);
      `uvm_info(`gfn, $sformatf("upstream received host spi item:\n%0s", item.sprint()),
                UVM_MEDIUM)
      if (cfg.en_cov) begin
        cov.all_modes_cg.sample(device_mode_e'(`gmv(ral.control.mode)), `gmv(ral.tpm_cfg.en));

        cov.cfg_settings_cg.sample(`gmv(ral.cfg.mailbox_en), `gmv(ral.cfg.tx_order),
                                    `gmv(ral.cfg.rx_order));
      end

      case (cfg.spi_host_agent_cfg.spi_func_mode)
        SpiModeFlash: begin
          internal_process_cmd_e cmd_type;
          bit is_intercepted;
          bit set_busy;
          `DV_CHECK(`gmv(ral.control.mode) inside {FlashMode, PassthroughMode})

          // read buffer is handled at `process_read_buffer_cmd`
          if (!cfg.is_read_buffer_cmd(item)) begin
            // downstream item should be in the queue at the same time, add small delay
            #1ps;
            cmd_type = triage_flash_cmd(item.opcode, set_busy);
            `uvm_info(`gfn,
                      $sformatf("%m - Triage flash cmd: %s, set_busy: %0d", cmd_type.name, set_busy),
                      UVM_MEDIUM)

            is_intercepted = 1;
            // InternalProcessStatus is handled by its own process
            if (cmd_type != InternalProcessStatus) begin
              case (cmd_type)
                NoInternalProcess: begin
                  is_intercepted = 0;
                end
                InternalProcessJedec: begin
                  check_internal_processed_read_jedec(item);
                end
                InternalProcessSfdp: begin
                  check_internal_processed_read_sfdp(item);
                end
                InternalProcessReadCmd: begin
                  spi_item downstream_item;
                  if (is_opcode_passthrough(item.opcode)) begin
                    // if busy, passthrough is blocked
                    if (!`gmv(ral.flash_status.busy)) begin
                      `DV_CHECK_EQ_FATAL(spi_passthrough_downstream_q.size, 1)
                      downstream_item = spi_passthrough_downstream_q[0];
                    end
                    else begin
                      `uvm_info(`gfn, {"flash txn was passthru. However, passtrough gate is closed",
                                       "due to busy set: ",
                                       $sformatf("spi_passthrough_downstream_q.size = %0d",
                                                 spi_passthrough_downstream_q.size)}, UVM_DEBUG)
                    end
                  end
                  check_read_cmd_data_for_non_read_buffer(item, downstream_item);
                end
                InternalProcessCfgCmd: begin
                  bit prev_wel = `gmv(ral.flash_status.wel);
                  if (`GET_OPCODE_VALID_AND_MATCH(cmd_info_en4b, item.opcode)) begin
                    if (cfg.en_cov)
                      cov.en4b_block_cmd_cg.sample(spi_side_fs_busy_at_csb_low);
                    //The busy bit is latched at CSB deassertion
                    if (!spi_side_fs_busy_at_csb_low) begin
                      if (cfg.en_cov) begin
                        cov.spi_device_addr_4b_enter_exit_command_cg.sample( .addr_4b_en(1),
                          .prev_addr_4b_en(`gmv(ral.addr_mode.addr_4b_en)));
                      end
                      void'(ral.addr_mode.addr_4b_en.predict(.value(1), .kind(UVM_PREDICT_WRITE)));
                      `uvm_info(`gfn, "Enable 4b addr due to cmd EN4B", UVM_MEDIUM)
                      cfg.spi_host_agent_cfg.flash_addr_4b_en = ral.addr_mode.addr_4b_en.get();
                      cfg.spi_device_agent_cfg.flash_addr_4b_en = ral.addr_mode.addr_4b_en.get();

                      spi_side_addr_mode_addr_4b_en = 1;
                      if (tl_ul_side_addr_mode_pending &&
                          tl_ul_side_addr_mode_addr_4b_en != 1) begin
                        `uvm_info(`gfn, "Write to ADDR_mode colliding with this EN4B flash command",
                                  UVM_DEBUG)
                        tl_ul_side_addr_mode_addr_4b_en = 1;
                        if (cfg.en_cov) begin
                          cov.en4b_flash_cmd_clash_with_addr_mode_write_cg.sample(1);
                        end
                      end
                    end
                  end else if (`GET_OPCODE_VALID_AND_MATCH(cmd_info_ex4b, item.opcode)) begin
                    if (cfg.en_cov)
                      cov.ex4b_block_cmd_cg.sample(spi_side_fs_busy_at_csb_low);

                    //The busy bit is latched at CSB deassertion
                    if (!spi_side_fs_busy_at_csb_low) begin
                      if (cfg.en_cov) begin
                        cov.spi_device_addr_4b_enter_exit_command_cg.sample(.addr_4b_en(0),
                          .prev_addr_4b_en(`gmv(ral.addr_mode.addr_4b_en)));
                      end
                      void'(ral.addr_mode.addr_4b_en.predict(.value(0), .kind(UVM_PREDICT_WRITE)));
                      `uvm_info(`gfn, "Exit 4b addr due to cmd EN4B", UVM_MEDIUM)
                      cfg.spi_host_agent_cfg.flash_addr_4b_en = ral.addr_mode.addr_4b_en.get();
                      cfg.spi_device_agent_cfg.flash_addr_4b_en = ral.addr_mode.addr_4b_en.get();

                      spi_side_addr_mode_addr_4b_en = 0;
                      if (tl_ul_side_addr_mode_pending && tl_ul_side_addr_mode_addr_4b_en != 0) begin
                        `uvm_info(`gfn, "Write to ADDR_mode colliding with this EX4B flash command",
                                  UVM_DEBUG)
                        tl_ul_side_addr_mode_addr_4b_en = 0;
                        if (cfg.en_cov) begin
                          cov.ex4b_flash_cmd_clash_with_addr_mode_write_cg.sample(1);
                        end
                      end
                    end // if (!spi_side_flash_status.busy)

                  end else if (`GET_OPCODE_VALID_AND_MATCH(cmd_info_wren, item.opcode)) begin

                    if (cfg.en_cov)
                      cov.wren_block_cmd_cg.sample(spi_side_fs_busy_at_csb_low);

                    //The busy bit is latched at CSB deassertion
                    if (!spi_side_fs_busy_at_csb_low) begin
                      // It could happen there is a flash_status write prior to WREN command finishing.
                      // What happens depends on when exactly the written flash value crosses
                      // boundaries towards the SCK side. So, in some cases, the WEL bit will be set
                      // on that written value, and in others it won't.
                      // SW note: This is not an actual concern since SW won't operate this way. In
                      // reality, SW won't be changing busy/wel bits unless the host is known to be
                      // waiting for busy/wel to drop (via sending flash READ_STATUS commands) os the
                      // host is held in reset.
                      `uvm_info(`gfn, "Updating WEL (0x1)", UVM_DEBUG)
                      update_wel = 1;
                      wel_val = 1;
                      spi_side_flash_status.wel = 1;
                      rtl_committed_flash_status = fetch_flash_status_rtl_committed_value();

                      // Update flash_status.wel predicted value
                      `DV_CHECK_EQ_FATAL(ral.flash_status.wel.predict(.value(
                        spi_side_flash_status.wel),.kind(UVM_PREDICT_READ)), 1,
                                         "ral.flash_status.predict did not succeed")
                      `uvm_info(`gfn,$sformatf("Updated the TL-UL flash_status.wel CSR to: %p",
                                               spi_side_flash_status.wel), UVM_DEBUG)

                      foreach (tl_ul_fuzzy_flash_status_q[i]) begin
                        if (rtl_committed_flash_status == tl_ul_fuzzy_flash_status_q[i]) begin
                          `uvm_info(`gfn, {$sformatf("The last flash_status written value (0x%0x)",
                                                     tl_ul_fuzzy_flash_status_q[i]),
                                           "ocurred before this WREN command - but hasn't crossed",
                                           "CDC boundaries until now and hence WEL won't be set"},
                                    UVM_DEBUG)
                          break;
                        end // if (rtl_committed_flash_status == tl_ul_fuzzy_flash_status_q[i])
                        if ((rtl_committed_flash_status.other_status ==
                             tl_ul_fuzzy_flash_status_q[i].other_status) &&
                            rtl_committed_flash_status.wel &&
                            !tl_ul_fuzzy_flash_status_q[i].wel) begin
                          `uvm_info(`gfn, {"Setting WEL bit in tl_ul_fuzzy_flash_status_q[i]",
                                           $sformatf("=0x%0x", tl_ul_fuzzy_flash_status_q[i])},
                                    UVM_DEBUG)
                          tl_ul_fuzzy_flash_status_q[i].wel = 1;
                        end

                      end // foreach (tl_ul_fuzzy_flash_status_q[i])
                      end // if (!spi_side_flash_status.busy)

                  end else if (`GET_OPCODE_VALID_AND_MATCH(cmd_info_wrdi, item.opcode)) begin

                    if (cfg.en_cov)
                      cov.wrdi_block_cmd_cg.sample(spi_side_fs_busy_at_csb_low);

                    //The busy bit is latched at CSB deassertion
                    if (!spi_side_fs_busy_at_csb_low) begin
                      `uvm_info(`gfn, "Updating WEL (0x0)", UVM_DEBUG)
                      update_wel = 1;
                      wel_val = 0;
                      spi_side_flash_status.wel = 0;
                      rtl_committed_flash_status = fetch_flash_status_rtl_committed_value();

                      foreach (tl_ul_fuzzy_flash_status_q[i]) begin
                        if (rtl_committed_flash_status == tl_ul_fuzzy_flash_status_q[i]) begin

                          `uvm_info(`gfn, {$sformatf("The last flash_status written value (0x%0x)",
                                                     tl_ul_fuzzy_flash_status_q[i]),
                                           "ocurred before this WRDI command - but hasn't crossed",
                                           "CDC boundaries until now and hence WEL won't be set"
                                           }
                                    ,
                                    UVM_DEBUG)
                          break;
                        end
                        if ( (rtl_committed_flash_status.other_status ==
                              tl_ul_fuzzy_flash_status_q[i].other_status) &&
                             !rtl_committed_flash_status.wel &&
                             tl_ul_fuzzy_flash_status_q[i].wel) begin
                          `uvm_info(`gfn, {"Setting WEL bit in tl_ul_fuzzy_flash_status_q[i]",
                                           $sformatf("=0x%0x", tl_ul_fuzzy_flash_status_q[i])},
                                    UVM_DEBUG)
                          tl_ul_fuzzy_flash_status_q[i].wel = 0;
                        end
                      end


                      // Update flash_status.wel predicted value
                      `DV_CHECK_EQ_FATAL( ral.flash_status.wel.predict(.value(
                        spi_side_flash_status.wel),.kind(UVM_PREDICT_READ)), 1,
                                          "ral.flash_status.predict did not succeed")
                      `uvm_info(`gfn,$sformatf("Updated the TL-UL flash_status.wel CSR to: %p",
                                               spi_side_flash_status.wel), UVM_DEBUG)


                    end // if (!spi_side_flash_status.busy)

                  end else begin
                    `uvm_fatal(`gfn, $sformatf("shouldn't enter here, opcode 0x%0x", item.opcode))
                  end
                  if (cfg.en_cov && update_wel) begin
                    cov.spi_device_write_enable_disable_cg.sample(wel_val, prev_wel);
                  end
                end
                UploadCmd: begin
                  process_upload_cmd(item);
                end
                default: `uvm_fatal(`gfn, "can't get here")
              endcase
            end // if (cmd_type == InternalProcessStatus)

            if (is_opcode_passthrough(item.opcode)) begin
              // if busy, passthrough is blocked
              if (!`gmv(ral.flash_status.busy)) begin
                `uvm_info(`gfn, "This is a Passthrough command and busy is not set", UVM_DEBUG)
                compare_passthru_item(.upstream_item(item), .is_intercepted(is_intercepted));
              end
              else begin
                `uvm_info(`gfn, {"flash txn was passthru. However, passtrough gate is closed due to",
                                 $sformatf(" busy set: spi_passthrough_downstream_q.size = %0d",
                                           spi_passthrough_downstream_q.size)}, UVM_DEBUG)
              end
            end // if (is_opcode_passthrough(item.opcode))

            // Updating BUSY below, otherwise it compromises the previous comparison
            if (set_busy) begin
              flash_status_t fs;
              spi_side_flash_status.busy = 1;
              `uvm_info(`gfn, "Setting 'spi_side_flash_status.busy'", UVM_DEBUG)
              `DV_CHECK_EQ_FATAL( ral.flash_status.busy.predict(.value(
                                  spi_side_flash_status.busy),.kind(UVM_PREDICT_READ)), 1,
                                  "ral.flash_status.predict did not succeed")
              `uvm_info(`gfn,$sformatf("Updated the TL-UL flash_status.busy CSR to: %p",
                                       spi_side_flash_status.busy), UVM_DEBUG)

              cfg.last_flash_cmd_set_busy = 1;
              `uvm_info(`gfn, "'cfg.last_flash_cmd_set_busy' set to help seqs 'busy' visibility",
                        UVM_DEBUG)

              // After setting the SCK busy bit due to a command info (upload+valid+busy)
              // we tweak all of the predictions accordingly
              foreach(tl_ul_side_flash_status_q[i]) begin
                $display("tl_ul_side_flash_status_q[i] = 0x%0x",tl_ul_side_flash_status_q[i]);
                fs = tl_ul_side_flash_status_q[i];
                tl_ul_side_flash_status_q[i].busy = 1;
                tl_ul_side_flash_status_q[i].wel = spi_side_flash_status.wel;
                `uvm_info(`gfn, {"Tweaking predicted flash_status due to last command setting  busy"
                  ," - ",$sformatf(
                  "OLD:tl_ul_side_flash_status_q[i]=0x%0x | NEW: tl_ul_side_flash_status_q[i]=0x%0x"
                  ,fs, tl_ul_side_flash_status_q[i])}, UVM_DEBUG)
              end

              foreach(tl_ul_fuzzy_flash_status_q[i]) begin
                $display("tl_ul_fuzzy_flash_status_q[i] = 0x%0x",tl_ul_fuzzy_flash_status_q[i]);
                fs = tl_ul_fuzzy_flash_status_q[i];
                tl_ul_fuzzy_flash_status_q[i].busy = 1;
                tl_ul_fuzzy_flash_status_q[i].wel = spi_side_flash_status.wel;
                `uvm_info(`gfn, {"Tweaking predicted flash_status due to last command setting  busy"
                  ," - OLD:",$sformatf(
                  "tl_ul_fuzzy_flash_status_q[i]=0x%0x | NEW: tl_ul_fuzzy_flash_status_q[i]=0x%0x"
                  ,fs, tl_ul_fuzzy_flash_status_q[i])}, UVM_DEBUG)
              end
            end // if (set_busy)

          end // if (!cfg.is_read_buffer_cmd(item))

          if (cfg.en_cov) begin : handle_fcov
            bit is_filter = !is_opcode_passthrough(item.opcode);
            if (`gmv(ral.flash_status.busy)) begin
              cov.flash_command_while_busy_set_cg.sample(is_filter);
            end
            if (cfg.spi_host_agent_cfg.is_opcode_supported(item.opcode)) begin
              spi_flash_cmd_info info = cfg.spi_host_agent_cfg.cmd_infos[item.opcode];
              spi_device_reg_cmd_info reg_cmd_info = cfg.get_cmd_info_reg_by_opcode(item.opcode);
              bit is_flash = `gmv(ral.control.mode) == FlashMode;
              bit addr_swap_en, payload_swap_en, upload, busy;
              if (reg_cmd_info != null) begin
                addr_swap_en = `gmv(reg_cmd_info.addr_swap_en);
                payload_swap_en = `gmv(reg_cmd_info.payload_swap_en);
                upload = `gmv(reg_cmd_info.upload);
                busy = `gmv(reg_cmd_info.busy);
              end

              cov.flash_cmd_info_cg.sample(
                  is_flash, item.opcode, item.write_command, info.addr_mode, addr_swap_en,
                  payload_swap_en, upload, busy, info.dummy_cycles, info.num_lanes);

              if (!is_flash) begin // passthrough
                bit [TL_DW-1:0] addr_mask = `gmv(ral.addr_swap_mask);
                bit [TL_DW-1:0] addr_data = `gmv(ral.addr_swap_data);
                bit [TL_DW-1:0] payload_mask = `gmv(ral.payload_swap_mask);
                bit [TL_DW-1:0] payload_data = `gmv(ral.payload_swap_data);

                cov.passthrough_addr_swap_cg.sample(addr_swap_en, addr_data, addr_mask);
                cov.passthrough_payload_swap_cg.sample(payload_swap_en, payload_data, payload_mask);
              end
              cov.passthrough_cmd_filter_cg.sample(item.opcode, is_filter);
              cov.flash_read_commands_cg.sample(item.opcode, info.dummy_cycles, is_filter,
                                                item.payload_q.size, is_intercepted);
            end
            if (`gmv(ral.tpm_cfg.en)) begin
              cov.tpm_interleave_with_flash_item_cg.sample(.is_tpm_item(0), .is_flash_item(1));
            end
          end : handle_fcov

        end
        SpiModeTpm: begin
          bit [TPM_ADDR_WIDTH-1:0] addr = convert_addr_from_byte_queue(item.address_q);
          bit is_hw_return;
          if (item.write_command) begin
            bit [31:0] wrfifo_start_addr = get_converted_addr(
              ral.ingress_buffer.get_offset() + 4 * spi_device_reg_pkg::SramTpmWrFifoOffset);
            foreach (item.data[i]) begin
              uvm_reg_addr_t addr = wrfifo_start_addr + i;

              spi_mem.write_byte(addr, item.data[i]);
              `uvm_info(`gfn, $sformatf("write tpm payload idx %0d, mem addr 0x%0x, val: 0x%0x",
                        i, addr, item.data[i]), UVM_MEDIUM)
            end
            update_pending_intr_w_delay(TpmHeaderNotEmpty);
          end else begin
            bit [TL_DW-1:0] exp_q[$];
            is_hw_return = is_tpm_reg(addr, item.read_size, exp_q);

            if (is_hw_return) begin
              compare_tpm_hw_reg(item.data, exp_q, addr[1:0]);
            end else begin
              `DV_CHECK_EQ(tpm_read_sw_q.size, 1)
              tpm_item_compare(item, tpm_read_sw_q.pop_front(), "read");
            end
          end
          if (cfg.en_cov) begin : tpm_cov
            bit [TPM_ADDR_WIDTH-1:0] aligned_addr = addr;
            bit [TPM_OFFSET_WIDTH-1:0] aligned_offset = {addr[TPM_OFFSET_WIDTH-1:2], 2'd0};
            bit is_in_tpm_region, is_valid_locality, is_hw_reg_offset, is_word_aligned;
            int locality = get_locality_from_addr(addr);

            aligned_addr[1:0] = 0;
            is_in_tpm_region = (addr inside {[24'hD4_0000:24'hD4_FFFF]});
            is_valid_locality = (
                addr[TPM_OFFSET_WIDTH+TPM_LOCALITY_WIDTH-1:TPM_OFFSET_WIDTH] < MAX_TPM_LOCALITY);
            is_hw_reg_offset = (
                aligned_addr[TPM_OFFSET_WIDTH-1:0] inside {ALL_TPM_HW_REG_OFFSETS});
            is_word_aligned = (addr[1:0] == 0);
            cov.tpm_cfg_cg.sample(tpm_cfg_mode_e'(`gmv(ral.tpm_cfg.tpm_mode)),
                                  `gmv(ral.tpm_cfg.hw_reg_dis),
                                  `gmv(ral.tpm_cfg.tpm_reg_chk_dis),
                                  `gmv(ral.tpm_cfg.invalid_locality),
                                  item.write_command,
                                  is_in_tpm_region,
                                  is_valid_locality,
                                  is_hw_reg_offset,
                                  is_word_aligned);
            cov.tpm_transfer_size_cg.sample(item.write_command, is_hw_return, item.data.size);

            if (aligned_offset == TPM_STS_OFFSET && locality < MAX_TPM_LOCALITY) begin
              bit active = cfg.get_locality_active(locality);
              cov.tpm_sts_cg.sample(item.write_command, active, is_hw_return, locality);
            end

            if (`gmv(ral.control.mode) inside {FlashMode, PassthroughMode}) begin
              cov.tpm_interleave_with_flash_item_cg.sample(.is_tpm_item(1), .is_flash_item(0));
            end
          end : tpm_cov
        end
        default: `uvm_fatal(`gfn, $sformatf("Unexpected mode: %0d",
                                            cfg.spi_host_agent_cfg.spi_func_mode))
      endcase
    end // forever
  endtask

  virtual function void tpm_item_compare(spi_item from_spi, spi_item from_sw, string msg);
    if (!from_spi.compare(from_sw)) begin
      `uvm_error(`gfn, $sformatf("Compare failed TPM %s, SPI item:\n%s SW item:\n%s",
            msg, from_spi.sprint(), from_sw.sprint()))
    end
  endfunction

  // if the reg is smaller than 32 bit, padding with all 1s at MSB
  function bit[TL_DW-1:0] get_reg_val_with_all_1s_padding(bit[TL_DW-1:0] val, uint num_bytes);
    for (int i = num_bytes; i < 4; i++) val[8*i +: 8] = '1;
    return val;
  endfunction

  function bit is_match_to_tpm_base_addr(bit[TPM_ADDR_WIDTH-1:0] addr);
    bit [TPM_ADDR_WIDTH-1:0] base_addr = addr & TPM_BASE_ADDR_MASK;
    return (base_addr == TPM_BASE_ADDR);
  endfunction

  `define CREATE_TPM_CASE_STMT(TPM_NAME, CSR_NAME) \
    ``TPM_NAME``_OFFSET: begin \
      exp_value_q.push_back(get_reg_val_with_all_1s_padding(`gmv(ral.``CSR_NAME``), \
                                                            ``TPM_NAME``_BYTE_SIZE)); \
      if (tpm_hw_reg_pre_val_aa.exists(`"CSR_NAME`")) begin \
        exp_value_q.push_back(get_reg_val_with_all_1s_padding( \
          tpm_hw_reg_pre_val_aa[`"CSR_NAME`"], ``TPM_NAME``_BYTE_SIZE)); \
      end \
      if (cfg.en_cov) cov.tpm_read_hw_reg_cg_wraps[`"CSR_NAME`"].sample(); \
    end
  // return 1 and exp SPI return data if the TPM read value is directly from HW-returned registers
  function automatic bit is_tpm_reg(bit [TPM_ADDR_WIDTH-1:0] addr,
                                    uint read_size,
                                    output bit [TL_DW-1:0] exp_value_q[$]);
    bit base_addr_match = is_match_to_tpm_base_addr(addr);
    bit [TPM_OFFSET_WIDTH-1:0] aligned_offset;
    int locality;
    bit [TL_DW-1:0] reg_val;

    // CRB mode doesn't return directly from HW
    if (`gmv(ral.tpm_cfg.tpm_mode) == TpmCrbMode) return 0;
    // if chk isn't disabled, it needs to match the base addr
    if (!`gmv(ral.tpm_cfg.tpm_reg_chk_dis) && !base_addr_match) begin
      return 0;
    end

    locality = get_locality_from_addr(addr);

    // handle invalid locality
    if (locality >= MAX_TPM_LOCALITY) begin
      if (`gmv(ral.tpm_cfg.invalid_locality)) begin
        exp_value_q = {'1};
        `uvm_info(`gfn, "return 'hff due to invalid locality", UVM_MEDIUM)
        return 1;
      end
      return 0;
    end

    // if hw_reg is disabled, return 0 and the request will be uploaded
    if (`gmv(ral.tpm_cfg.hw_reg_dis)) return 0;

    aligned_offset = {addr[TPM_OFFSET_WIDTH-1:2], 2'd0};
    // if locality is inactive, return 'hff for TPM_STS
    if (aligned_offset == TPM_STS_OFFSET) begin
      bit cur_locality_active = cfg.get_locality_active(locality);
      bit pre_locality_active = cur_locality_active;
      string access_name = $sformatf("tpm_access_%0d", locality);

      if (tpm_hw_reg_pre_val_aa.exists(access_name)) begin
        pre_locality_active = tpm_hw_reg_pre_val_aa[access_name][TPM_ACTIVE_LOCALITY_BIT_POS];
        `uvm_info(`gfn, $sformatf("%s = 0x%0x", access_name, tpm_hw_reg_pre_val_aa[access_name]),
                  UVM_MEDIUM)
      end
      if (!cur_locality_active || !pre_locality_active) exp_value_q = {'1};
      `uvm_info(`gfn, "return 'hff due to reading TPM_STS on an inactive locality", UVM_MEDIUM)

      // when both are inactive, return. Otherwise, it has more than 1 exp value
      if (!cur_locality_active && !pre_locality_active) return 1;
    end

    case (aligned_offset)
      TPM_ACCESS_OFFSET: begin
        string access_reg_name = $sformatf("tpm_access_%0d", locality);
        const int size = 1;

        reg_val = `gmv(cfg.get_tpm_access_reg_field(locality));
        reg_val = get_reg_val_with_all_1s_padding(reg_val, size);
        exp_value_q.push_back(reg_val);

        if (tpm_hw_reg_pre_val_aa.exists(access_reg_name)) begin
          reg_val = get_reg_val_with_all_1s_padding(tpm_hw_reg_pre_val_aa[access_reg_name], size);
          exp_value_q.push_back(reg_val);
        end
        if (cfg.en_cov) cov.tpm_read_hw_reg_cg_wraps[access_reg_name].sample();
      end
      TPM_HASH_START_OFFSET: begin
        exp_value_q = {'1};
        if (cfg.en_cov) cov.tpm_read_hw_reg_cg_wraps["tpm_hash_start"].sample();
      end
      `CREATE_TPM_CASE_STMT(TPM_INT_ENABLE, tpm_int_enable)
      `CREATE_TPM_CASE_STMT(TPM_INT_VECTOR, tpm_int_vector)
      `CREATE_TPM_CASE_STMT(TPM_INT_STATUS, tpm_int_status)
      `CREATE_TPM_CASE_STMT(TPM_INTF_CAPABILITY, tpm_intf_capability)
      `CREATE_TPM_CASE_STMT(TPM_STS, tpm_sts)
      `CREATE_TPM_CASE_STMT(TPM_DID_VID, tpm_did_vid)
      `CREATE_TPM_CASE_STMT(TPM_RID, tpm_rid)
      default: return 0;
    endcase

    `uvm_info(`gfn, $sformatf("Read on the hw-returned reg, addr 0x%0x, data %p",
                              addr, exp_value_q), UVM_MEDIUM)
    return 1;
  endfunction : is_tpm_reg
  `undef CREATE_TPM_CASE_STMT

  // act_byte_q contains all received bytes data
  // exp_word_q shows all the possible values on word format as SW may program the HW regs during
  // the SPI transaction
  virtual function void compare_tpm_hw_reg(bit [7:0] act_byte_q[$], bit [TL_DW-1:0] exp_word_q[$],
                                           bit [1:0] addr_2lsb);
    int offset = addr_2lsb;
    bit [TL_DW-1:0] act_word;
    // have it align with addr_2lsb and same size as act_byte_q
    bit [TL_DW-1:0] updated_exp_word_q[$];
    for (int i = 0;  i < act_byte_q.size && offset < 4; i++, offset++) begin
      act_word[8*i +: 8] = act_byte_q[i];
      foreach (exp_word_q[j]) begin
        updated_exp_word_q[j][8*i +: 8] = exp_word_q[j][8*offset +: 8];
      end
    end
    if (!(act_word inside {updated_exp_word_q})) begin
      `uvm_error(`gfn, $sformatf("Compare TPM reg failed, offset: %0d, act: 0x%0x, exp: %p",
                                addr_2lsb, act_word, updated_exp_word_q))
    end
  endfunction : compare_tpm_hw_reg


  // this only triages post-process cmd. read buffer cmd isn't handled here as it needs to be
  // processed during transaction.
  virtual function internal_process_cmd_e triage_flash_cmd(bit[7:0] opcode, output bit set_busy);
    internal_process_cmd_e cmd_type;
    bit is_status, is_jedec, is_sfdp;
    bit is_passthru = `gmv(ral.control.mode) == PassthroughMode;
    spi_device_reg_cmd_info reg_cmd_info = cfg.get_cmd_info_reg_by_opcode(opcode);

    `uvm_info(`gfn, $sformatf("Triaging flash command (op=0x%0x)",opcode), UVM_DEBUG)
    set_busy = 0;
    if (reg_cmd_info != null && `gmv(reg_cmd_info.upload)) begin

      if (cfg.en_cov)
        cov.upload_block_cmd_cg.sample(spi_side_fs_busy_at_csb_low);

      if (!spi_side_fs_busy_at_csb_low) begin
        if (`gmv(reg_cmd_info.busy)) set_busy = 1;
        return UploadCmd;
      end
      else
        `uvm_info(`gfn, "Command info ignored due to busy bit being set", UVM_DEBUG)
    end

    is_status = opcode inside {READ_STATUS_1, READ_STATUS_2, READ_STATUS_3} &&
                cfg.is_internal_recog_cmd(opcode);
    if (is_passthru) is_status &= `gmv(ral.intercept_en.status);
    if (is_status) return InternalProcessStatus;

    is_jedec = opcode == READ_JEDEC && `gmv(ral.intercept_en.jedec) &&
              cfg.is_internal_recog_cmd(opcode);
    if (is_passthru) is_jedec &= `gmv(ral.intercept_en.jedec);
    if (is_jedec) return InternalProcessJedec;

    is_sfdp = opcode == READ_SFDP &&
              cfg.is_internal_recog_cmd(opcode);
    if (is_passthru) is_sfdp &= `gmv(ral.intercept_en.sfdp);
    if (is_sfdp) return InternalProcessSfdp;

    if (opcode inside {READ_CMD_LIST} && cfg.is_internal_recog_cmd(opcode)) begin
      return InternalProcessReadCmd;
    end

    if (cfg.is_internal_cfg_cmd(opcode)) return InternalProcessCfgCmd;

    return NoInternalProcess;
  endfunction

  virtual function bit is_opcode_passthrough(bit[7:0] opcode);
    int cmd_index = get_cmd_filter_index(opcode);
    int cmd_offset = get_cmd_filter_offset(opcode);
    bit filter = `gmv(ral.cmd_filter[cmd_index].filter[cmd_offset]);
    bit valid_cmd = cfg.spi_host_agent_cfg.is_opcode_supported(opcode);

    if (`gmv(ral.control.mode) != PassthroughMode) return 0;

    `uvm_info(`gfn, $sformatf("opcode filter: %0d, valid: %0d", filter, valid_cmd), UVM_MEDIUM)
    return !filter && valid_cmd;
  endfunction

  virtual function void check_internal_processed_read_jedec(spi_item item);
    bit [7:0] exp_jedec_q[$];
    bit [15:0] id = `gmv(ral.jedec_id.id);
    bit [7:0]  mf = `gmv(ral.jedec_id.mf);

    repeat (`gmv(ral.jedec_cc.num_cc)) exp_jedec_q.push_back(`gmv(ral.jedec_cc.cc));

    exp_jedec_q.push_back(mf);
    exp_jedec_q.push_back(id[7:0]);
    exp_jedec_q.push_back(id[15:8]);

    foreach (item.payload_q[i]) begin
      if (i < exp_jedec_q.size) begin
        `DV_CHECK_CASE_EQ(item.payload_q[i], exp_jedec_q[i],
            $sformatf("act 0x%0x != exp 0x%0x, index: %0d", item.payload_q[i], exp_jedec_q[i], i))
      end else begin
        `DV_CHECK_CASE_EQ(item.payload_q[i], 0,
            $sformatf("act 0x%0x != exp 0x0, index: %0d (OOB)", item.payload_q[i], i))
      end
    end
  endfunction

  virtual function void check_internal_processed_read_sfdp(spi_item item);
    foreach (item.payload_q[i]) begin
      uvm_reg_addr_t addr, offset;

      // address should be 3 bytes, only the last byte is used
      `DV_CHECK_EQ(item.address_q.size, 3)
      offset = (item.address_q[2] + i) % SFDP_SIZE;

      compare_mem_byte(SFDP_START_ADDR, offset, item.payload_q[i], i, "SFDP");
    end
  endfunction

  virtual function void compare_mem_byte(bit [31:0] base_addr, bit [31:0] offset, bit[7:0] act_val,
                                         // these 2 inputs are for log only
                                         int payload_idx, string msg);
    bit [31:0] addr = get_converted_addr(base_addr + offset);
    `uvm_info(`gfn, $sformatf("Converted Addr = 0x%0x",addr), UVM_DEBUG)
    `DV_CHECK(spi_mem.addr_exists(addr))
    spi_mem.compare_byte(addr, act_val);
      `uvm_info(`gfn, $sformatf(
                "%s compare idx: %0d, offset %0d, mem addr 0x%0x, act: 0x%0x, exp: 0x%0x",
                msg, payload_idx, offset, addr, act_val, spi_mem.read_byte(addr)), UVM_MEDIUM)
  endfunction

  // check read return data again exp_mem or downstream item
  // this doesn't handle read cmd falling in read buffer
  virtual function void check_read_cmd_data_for_non_read_buffer(spi_item up_item,
                                                                spi_item dn_item);
    bit [31:0] start_addr, cur_addr;
    bit is_passthru = `gmv(ral.control.mode) == PassthroughMode;
    // these vairables are for coverage collection
    read_addr_size_type_e read_addr_size_type;
    bit start_at_mailbox, end_at_mailbox, been_mailbox;

    foreach (up_item.address_q[i]) begin
      if (i > 0) start_addr = start_addr << 8;
      start_addr[7:0] = up_item.address_q[i];
    end
    start_addr = convert_addr_from_byte_queue(up_item.address_q);

    if (dn_item != null) begin
      // If the read_pipeline is enabled, there will be data latched on the pipe which won't
      // "come out" to the host because CSB has become inactive. This can be 2-bit, 4-bit or 8-bit
      // depending whether we're doing a "normal" READ, READDUAL, READQUAD.
      // Hence it's ok for the DS queue to be 1 item larger.

      if (up_item.read_pipeline_mode && up_item.payload_q.size == 0) begin
        // If the read_pipeline is enabled is possible the DS item has sampled some data
        // since it had 2 "extra cycles", it really depends on when the txn terminated.
        if (!((up_item.payload_q.size == dn_item.payload_q.size) ||
             (up_item.payload_q.size == dn_item.payload_q.size-1)))
          `uvm_error(`gfn, {"DS and US items don't have the same payload size" , $sformatf(
                            " (US - %0d) (DS - %0d)", up_item.payload_q.size,
                            dn_item.payload_q.size )})
      end
      else begin
        int unsigned dn_item_payload_size = dn_item.payload_q.size;
        // We expect the payload for up_item to be one byte shorter than the payload for dn_item,
        // in some cases with the read pipeline mode enabled
        if (up_item.read_pipeline_mode>0 && (dn_item.payload_q.size > up_item.payload_q.size))
          dn_item_payload_size--;

        `DV_CHECK_EQ(up_item.payload_q.size, dn_item_payload_size)
      end
    end // if (dn_item != null)


    foreach (up_item.payload_q[i]) begin
      cur_addr = start_addr + i;

      if (cfg.is_in_mailbox_region(cur_addr)) begin
        bit [31:0] offset = cur_addr % MAILBOX_BUFFER_SIZE;
        `uvm_info(`gfn, {"Command has been intercepted and is in the MBX region",
                         $sformatf("MAILBOX_START_ADDR = 0x%0x - offset = 0x%0x",MAILBOX_START_ADDR,
                                   offset)
                         },
                  UVM_DEBUG)
        compare_mem_byte(MAILBOX_START_ADDR, offset, up_item.payload_q[i], i, "Mailbox");
        if (i == 0) start_at_mailbox = 1;
        been_mailbox = 1;
      end else begin // out of mbx region
        string str;

        `DV_CHECK_EQ_FATAL(is_passthru, 1)
        if (dn_item != null) begin
          str = $sformatf("compare US data with DS item. idx %0d, up: 0x%0x, dn: 0x%0x",
                          i, up_item.payload_q[i], dn_item.payload_q[i]);
          `DV_CHECK_CASE_EQ(up_item.payload_q[i], dn_item.payload_q[i], str)
        end else begin // cmd is filtered
          str = $sformatf("compare US data - command was filtered. idx %0d, value 0x%0x != z",
                          i, up_item.payload_q[i]);
          `DV_CHECK_CASE_EQ(up_item.payload_q[i], 8'dz, str)
        end

        `uvm_info(`gfn, str, UVM_MEDIUM)
      end
    end

    if (cfg.is_in_mailbox_region(cur_addr)) end_at_mailbox = 1;
    if (cfg.en_cov) begin
      if (is_passthru) begin
        bit filtered = (dn_item == null);
        case ({start_at_mailbox, been_mailbox, end_at_mailbox})
          3'b111: read_addr_size_type = ReadAddrWithinMailbox;
          3'b011: read_addr_size_type = ReadAddrCrossIntoMailbox;
          3'b110: read_addr_size_type = ReadAddrCrossOutOfMailbox;
          3'b010: read_addr_size_type = ReadAddrCrossAllMailbox;
          3'b000: read_addr_size_type = ReadAddrOutsideMailbox;
          default: `uvm_fatal(`gfn, $sformatf("Unexpected values 0b%b",
                                            {start_at_mailbox, been_mailbox, end_at_mailbox}))
        endcase
        cov.passthrough_mailbox_cg.sample(up_item.opcode, read_addr_size_type, filtered);
      end else begin // flash mode
        cov.flash_mailbox_cg.sample(up_item.opcode);
      end
    end
  endfunction

  virtual function void process_upload_cmd(spi_item item);
    bit [31:0] payload_start_addr = get_converted_addr(ral.ingress_buffer.get_offset());
    int payload_depth_exp;
    upload_cmd_q.push_back(item.opcode);
    update_pending_intr_w_delay(.intr(CmdFifoNotEmpty), .delay_cyc(4));

    if (item.address_q.size > 0) begin
      bit[31:0] addr = convert_addr_from_byte_queue(item.address_q);
      upload_addr_q.push_back(addr);
    end

    foreach (item.payload_q[i]) begin
      uvm_reg_addr_t addr = payload_start_addr + (i % PAYLOAD_FIFO_SIZE);

      spi_mem.write_byte(addr, item.payload_q[i]);
      `uvm_info(`gfn, $sformatf("write upload payload idx %0d, mem addr 0x%0x, val: 0x%0x",
                i, addr, item.payload_q[i]), UVM_MEDIUM)
    end
    if (item.payload_q.size > 0) update_pending_intr_w_delay(PayloadNotEmpty);

    update_cmdfifo_status();
    update_addrfifo_status();

    if (item.payload_q.size > PAYLOAD_FIFO_SIZE) begin // overflow
      payload_depth_exp = PAYLOAD_FIFO_SIZE;
      intr_trigger_pending[PayloadOverflow] = 1;
    end else begin
      payload_depth_exp = item.payload_q.size;
    end
    payload_depth_exp = item.payload_q.size > 256 ? 256 : item.payload_q.size;
    void'(ral.upload_status2.payload_depth.predict(.value(payload_depth_exp),
                                                   .kind(UVM_PREDICT_READ)));
    // if received payload is bigger than fifo size, payload_start_idx = payload size % fifo size.
    if (item.payload_q.size > PAYLOAD_FIFO_SIZE) begin
      int start_idx = item.payload_q.size % PAYLOAD_FIFO_SIZE;
      void'(ral.upload_status2.payload_start_idx.predict(.value(start_idx),
                                                         .kind(UVM_PREDICT_READ)));
    end else begin
      void'(ral.upload_status2.payload_start_idx.predict(.value(0), .kind(UVM_PREDICT_READ)));
    end

    if (cfg.en_cov) begin
      cov.flash_upload_payload_size_cg.sample(item.write_command, item.payload_q.size);
    end
  endfunction

  virtual function void update_cmdfifo_status();
    void'(ral.upload_status.cmdfifo_depth.predict(.value(upload_cmd_q.size),
                                                  .kind(UVM_PREDICT_READ)));
    void'(ral.upload_status.cmdfifo_notempty.predict(.value(upload_cmd_q.size > 0),
                                                  .kind(UVM_PREDICT_READ)));
  endfunction

  virtual function void update_addrfifo_status();
    void'(ral.upload_status.addrfifo_depth.predict(.value(upload_addr_q.size),
                                                  .kind(UVM_PREDICT_READ)));
    void'(ral.upload_status.addrfifo_notempty.predict(.value(upload_addr_q.size > 0),
                                                  .kind(UVM_PREDICT_READ)));
  endfunction

  // convert offset to the mem address that is used to find the locaiton in exp_mem
  // lsb 2 bit will be kept
  virtual function bit [31:0] get_converted_addr(bit [31:0] offset);
    return ral.get_normalized_addr(offset) + offset[1:0];
  endfunction

  virtual function void handle_addr_payload_swap(spi_item item);
    spi_device_reg_cmd_info reg_cmd_info = cfg.get_cmd_info_reg_by_opcode(item.opcode);
    if (reg_cmd_info == null) return;
    `uvm_info(`gfn, $sformatf("Addr/Payload Swap for cmd_info = %s",reg_cmd_info.get_name()),
              UVM_DEBUG)
    if (`gmv(reg_cmd_info.addr_swap_en)) begin
      bit [TL_DW-1:0] mask = `gmv(ral.addr_swap_mask);
      bit [TL_DW-1:0] data = `gmv(ral.addr_swap_data);

      `uvm_info(`gfn, $sformatf("Swap addr for opcode: 0x%0h, mask/data: 0x%0h/0x%0h, old: %p",
          item.opcode, mask, data, item.address_q), UVM_MEDIUM)
      foreach (item.address_q[i]) begin
        // address_q[0] is the first collected address, but actual address is from MSB to LSB
        // (first one received is the last byte of the address)
        int addr_idx = item.address_q.size - i - 1;
        item.address_q[i] = (item.address_q[i] & ~mask[addr_idx*8 +: 8]) |
                            (data[addr_idx*8 +: 8] & mask[addr_idx*8 +: 8]);
      end
       `uvm_info(`gfn, $sformatf("New addr: %p", item.address_q), UVM_MEDIUM)
    end

    if (`gmv(reg_cmd_info.payload_swap_en)) begin
      bit [TL_DW-1:0] mask = `gmv(ral.payload_swap_mask);
      bit [TL_DW-1:0] data = `gmv(ral.payload_swap_data);
      // swap up to 4 bytes
      int swap_byte_num = item.payload_q.size > 4 ? 4 : item.payload_q.size;

      `uvm_info(`gfn, $sformatf("Swap Payload for opcode: 0x%0h, mask/data: 0x%0h/0x%0h, old: %p",
          item.opcode, mask, data, item.payload_q[0:swap_byte_num]), UVM_MEDIUM)
      for (int i = 0; i < swap_byte_num; i++) begin
        item.payload_q[i] = (item.payload_q[i] & ~mask[i*8 +: 8]) |
                            (data[i*8 +: 8] & mask[i*8 +: 8]);
      end
      `uvm_info(`gfn, $sformatf("New payload: %p", item.payload_q[0:swap_byte_num]), UVM_MEDIUM)
    end
  endfunction

  virtual function void compare_passthru_item(spi_item upstream_item, bit is_intercepted);
    spi_item downstream_item;

    handle_addr_payload_swap(upstream_item);
    `uvm_info(`gfn, $sformatf("'compare_passthru_item': spi_passthrough_downstream_q.size = %0f",
                              spi_passthrough_downstream_q.size), UVM_DEBUG)
    `DV_CHECK_EQ_FATAL(spi_passthrough_downstream_q.size, 1)
    downstream_item = spi_passthrough_downstream_q.pop_front();

    if (is_intercepted) begin
      // compare opcode and address. data is ignored as data is checked in
      // check_read_cmd_data_for_non_read_buffer
      `DV_CHECK_EQ(upstream_item.opcode, downstream_item.opcode)
      `DV_CHECK_EQ(upstream_item.address_q.size, downstream_item.address_q.size)
      foreach (upstream_item.address_q[i]) begin
        `DV_CHECK_EQ(upstream_item.address_q[i], downstream_item.address_q[i])
      end
    end else begin

      if (upstream_item.read_pipeline_mode > 0 &&
         (downstream_item.payload_q.size == (upstream_item.payload_q.size+1))) begin
        // Read pipeline is enabled, so if the US item is 1 item short of payload bytes (due to CSB
        // becoming inactive and the "missing" data still in the read pipeline), we need to
        // "manually" compare the items (opcode, address, payload)
        `uvm_info(`gfn, {"Comparing only the number of payload items in US item (1 less than DS",
         " item) since read_pipeline is enabled"}, UVM_DEBUG);

        //compare opcode
        `DV_CHECK_CASE_EQ(upstream_item.opcode, downstream_item.opcode)
        //compare addr
        `DV_CHECK_EQ(upstream_item.address_q.size, downstream_item.address_q.size)
        foreach(upstream_item.address_q[i]) begin
          `DV_CHECK_CASE_EQ(upstream_item.address_q[i], downstream_item.address_q[i],
                            {"compare US address with DS item.", $sformatf(
                             " idx %0d, up: 0x%0x, dn: 0x%0x",i, upstream_item.address_q[i],
                             downstream_item.address_q[i])})

        end
        //compare payload
        foreach(upstream_item.payload_q[i]) begin
          `DV_CHECK_CASE_EQ(upstream_item.payload_q[i], downstream_item.payload_q[i],
                            {"compare US data with DS item.", $sformatf(
                             " idx %0d, up: 0x%0x, dn: 0x%0x",i, upstream_item.payload_q[i],
                             downstream_item.payload_q[i])})


        end
      end
      else if (!downstream_item.compare(upstream_item)) begin
        `uvm_error(`gfn, $sformatf("Compare failed, downstream item:\n%s upstream item:\n%s",
              downstream_item.sprint(), upstream_item.sprint()))
      end
    end
  endfunction

  // extract spi items sent from device
  virtual task process_upstream_spi_device_fifo();
    spi_item item;
    forever begin
      upstream_spi_device_fifo.get(item);
      sendout_spi_tx_data({item.data[3], item.data[2], item.data[1], item.data[0]});
      `uvm_info(`gfn, $sformatf("upstream received device spi item:\n%0s", item.sprint()), UVM_HIGH)
    end
  endtask

  virtual task process_downstream_spi_fifo();
    spi_item downstream_item;
    spi_item upstream_item;
    forever begin
      downstream_spi_host_fifo.get(downstream_item);
      `uvm_info(`gfn, $sformatf("downstream received spi item:\n%0s", downstream_item.sprint()),
                UVM_MEDIUM)
      `DV_CHECK_EQ(`gmv(ral.control.mode), PassthroughMode)
      `DV_CHECK_EQ(spi_passthrough_downstream_q.size, 0)
      spi_passthrough_downstream_q.push_back(downstream_item);
      `uvm_info(`gfn, {"After receiving passthrough item: spi_passthrough_downstream_q.size",
                       $sformatf(" = %0d",spi_passthrough_downstream_q.size)}, UVM_DEBUG)
    end
  endtask

  task check_addr_mode_propagation();
    bit rtl_pending, rtl_addr_4b_en;
    // 3-6 (and even up to 6 in certain scenarios due to CDC instrumentation variability) sys
    // cycles delay after the first byte of spi-data
    int unsigned cycle_delay = 6;

    forever begin
      wait(check_addr_mode_propagation_ev.triggered);
      `uvm_info(`gfn, "Event 'check_addr_mode_propagation_ev' triggered", UVM_DEBUG)

      if (!tl_ul_side_addr_mode_pending) begin
        // Adding some time consuming delay to avoid an infinite loop if
        // 'tl_ul_side_addr_mode_pending' is not set
        #(cfg.spi_host_agent_cfg.sck_period_ps/4 * 1ps);
        continue;
      end

      // Sys clk delay
      cfg.clk_rst_vif.wait_n_clks(cycle_delay);
      // Adding a SPI clock_cycle delay since the spi_item.byte_event may be triggered before RTL update
      #(cfg.spi_host_agent_cfg.sck_period_ps * 1ps);
      tl_ul_side_addr_mode_pending = 0;


      `uvm_info(`gfn, {"Carrying out ADDR_MODE check since there was a write and SPI Host",
                       " sent the first data byte"}, UVM_DEBUG)

      // Check the pending bit is set
      csr_rd(.ptr(ral.addr_mode.pending), .value(rtl_pending), .backdoor(1));

      `uvm_info(`gfn, "Checking pending bit has been unset", UVM_DEBUG)

      // We expect the pending bit to be unset at this time, hence compare against 0
      `DV_CHECK_EQ(rtl_pending, 0,
                   $sformatf("Comparison mismatch, act (0x%0x) != exp %p",
                             rtl_pending, tl_ul_side_addr_mode_pending))

      // Update flash_status predicted value
      `DV_CHECK_EQ_FATAL(ral.addr_mode.addr_4b_en.predict(.value(tl_ul_side_addr_mode_addr_4b_en),
                                                          .kind(UVM_PREDICT_READ)), 1,
                         "ral.addr_mode.addr_4b_en.predict did not succeed")
      spi_side_addr_mode_addr_4b_en = tl_ul_side_addr_mode_addr_4b_en;
      `uvm_info(`gfn, $sformatf("Updated TL-UL ADDR_MODE CSR to: ral.addr_mode.addr_4b_en=0x%0x",
                                tl_ul_side_addr_mode_addr_4b_en), UVM_DEBUG)

      `DV_CHECK_EQ_FATAL(ral.addr_mode.pending.predict(.value(0),
                                                       .kind(UVM_PREDICT_READ)), 1,
                         "ral.addr_mode.addr_4b_en.predict did not succeed")


      // Check if the RTL value has updated
      csr_rd(.ptr(ral.addr_mode.addr_4b_en), .value(rtl_addr_4b_en), .backdoor(1));
      `DV_CHECK_EQ(rtl_addr_4b_en, tl_ul_side_addr_mode_addr_4b_en,
                   $sformatf("ADDR_MODE.addr_4b_en Comparison mismatch, act (0x%0x) != exp %p",
                             rtl_addr_4b_en, tl_ul_side_addr_mode_addr_4b_en))

    end // forever begin
  endtask

  // RX TXN on CSB active and each of the sampled bytes of data as well as CSB becoming inactive
  // Checks for flash_status and addr_mode TL-UL to SCK side propagation and vice versa
  virtual task process_tl2spi_updates();
    forever begin
      bit first_byte = 1;
      spi_item spi_txn;
      flash_status_t old_flash_status, fs;

      upstream_csb_active_fifo.get(spi_txn);
      // Received TXN is used to know when to update TL-UL and SPI flash_status values The SPI side
      // updates on each 8th clock edge whereas the TL-UL side updates on CSB deassertion
      `uvm_info(`gfn, "CSB is now active (low)", UVM_DEBUG)
      spi_side_fs_busy_at_csb_low = spi_side_flash_status.busy;

      if (cfg.last_flash_cmd_set_busy) begin
        cfg.last_flash_cmd_set_busy = 0;
        `uvm_info(`gfn, "'cfg.last_flash_cmd_set_busy' unset to help seqs 'busy' visibility",
          UVM_DEBUG)
      end

      fork
        begin: isolation_thread
          fork
            begin
              // Exit if CSB becomes inactive
              wait (spi_txn.item_finished_ev.triggered);
              `uvm_info(`gfn, {"[spi_txn.item_finished_ev triggered] - CSB has gone inactive",
                               " - killing thread"}, UVM_DEBUG)

              // We only update the 'spi_side_flash_status' value here if there's not an ongoing
              // READ_STATUS flash_command. Otherwise, the TB will have a "new value" updated
              // too early to compare against the previously latched value in the parallel to
              // serial buffer in the RTL
              if (update_spi_side_flash_status_after_read_status &&
                 tl_ul_fuzzy_flash_status_q.size > 0) begin
                int queue_idx;
                flash_status_t rtl_sck_status_committed_value;
                // flash_status needs to be updated here, otherwise the busy bit may not be ready on
                // time for the passthrough gate busy check causing mismatches, but also can't be
                // updated earlier, otherwise it conflicts with the read value from READ_STATUS#1/2/3

                `uvm_info(`gfn, "Unset 'update_spi_side_flash_status_after_read_status'", UVM_DEBUG)
                update_spi_side_flash_status_after_read_status = 0;

                // Snoop into the RTL to see if TL-UL written values have yet been committed.
                // It'll depend on the exact moment in which the TL-UL flash_status value was
                // written. If it's been committed, then update spi_side.
                rtl_sck_status_committed_value = fetch_flash_status_rtl_committed_value();

                if (flash_sts_committed_in_q(tl_ul_fuzzy_flash_status_q,1, 1,queue_idx)) begin
                  `uvm_info(`gfn, {"old_value: spi_side_flash_status=", $sformatf(
                    "0x%0x | new_value: spi_side_flash_status=0x%0x", spi_side_flash_status,
                    tl_ul_fuzzy_flash_status_q[queue_idx])}
                            , UVM_DEBUG)

                  spi_side_flash_status = tl_ul_fuzzy_flash_status_q[queue_idx];
                  tl_ul_fuzzy_flash_status_q = tl_ul_fuzzy_flash_status_q[$:queue_idx+1];
                end
              end // if (update_spi_side_flash_status_after_read_status &&...

            end // fork begin
            begin
              int tl_ul_side_idx, tl_ul_fuzzy_idx;
              bit comitted_value_predicted;
              bit committed_value_in_tl_ul_side;
              bit committed_value_in_tl_ul_fuzzy_side;
              bit wel_compare, busy_compare;
              bit tl_ul_side_partial_match;
              forever begin
                // TXN.byte_sampled_ev triggered in FLASH mode only
                wait (spi_txn.byte_sampled_ev.triggered);
                `uvm_info(`gfn, "Event 'spi_txn.byte_sampled' has been triggered", UVM_DEBUG)

                if (first_byte) begin
                  first_byte = 0;
                  // ADDR_MODE updates on SCK side on the first byte of SPI flash txn
                  -> check_addr_mode_propagation_ev;
                end

                // task above is delay free since it's an infinite loop  within a fork...join_any
                // Adding some "SPI-side" clk_delay to ensure the triggering events are noticed
                #(cfg.spi_host_agent_cfg.sck_period_ps/4 * 1ps);
                `uvm_info(`gfn, $sformatf("tl_ul_side_flash_status_q.size %0d",
                                          tl_ul_side_flash_status_q.size), UVM_DEBUG)

                // If we've had writes (already in tl_ul_side_flash_status_q.size>0) unless for some
                // reason the write is not in the tl_ul_side_flash_status_q yet (due to TB delays)
                // In which case, we need to see if the tl_ul_fuzzy_q has any value different from
                // the GMV (which means there's been a write)


                // Note: depending on the clocks relationship, it may happen the RTL may commit a
                // value before the TB notices. The TB isn't trying to accurately predict when a
                // given value will be committed. Instead, the TB just checks from the set of
                // written values one of those has been comitted
                //
                // It can happen busy/wel bits may get set as the SPI txn goes through. In this
                // case we don't compare WEL/busy, as the value might've changed since the
                // flash_status write occurred
                comitted_value_predicted  = 0;

                // We look for an exact match first, and if there's not we then try to match the
                // upper-bits
                tl_ul_side_partial_match = 1;
                if (flash_sts_committed_in_q(tl_ul_side_flash_status_q, 1, 1, tl_ul_side_idx)) begin
                  committed_value_in_tl_ul_side = 1;
                  tl_ul_side_partial_match = 0;
                end
                else
                  committed_value_in_tl_ul_side = flash_sts_committed_in_q(tl_ul_side_flash_status_q,
                                                                         0, 0, tl_ul_side_idx);

                if (flash_sts_committed_in_q(tl_ul_fuzzy_flash_status_q,1, 1,tl_ul_fuzzy_idx)) begin
                  committed_value_in_tl_ul_fuzzy_side = 1;
                  // tl-ul_side Q has a partial match, but tl_ul_fuzzy Q has a perfect match.
                  // TB takes exact match
                  if (tl_ul_side_partial_match && tl_ul_side_idx!=-1) begin
                    tl_ul_side_idx = -1; //We invalidate the partial match, to take the full match
                  end
                end
                else begin
                  committed_value_in_tl_ul_fuzzy_side = flash_sts_committed_in_q(
                    tl_ul_fuzzy_flash_status_q,0, 0,tl_ul_fuzzy_idx);
                end
                comitted_value_predicted = committed_value_in_tl_ul_side |
                                           committed_value_in_tl_ul_fuzzy_side;

                if (comitted_value_predicted) begin
                  uvm_hdl_data_t 	rtl_sck_status_committed_value;
                  flash_status_t  f_status_rtl_committed_value;
                  // Queue rather than a plain variable to check emptiness before updating
                  // spi_side_flash_status
                  flash_status_t  flash_status_q[$];
                  f_status_rtl_committed_value = fetch_flash_status_rtl_committed_value();
                  // Based on the indices returned by 'flash_sts_committed_in_q' we know what
                  // to populate flash_status_q with
                  if (tl_ul_side_idx != -1) begin
                    flash_status_q.push_back(tl_ul_side_flash_status_q[tl_ul_side_idx]);
                    `uvm_info(`gfn, {"The RTL committed value is found in ",
                                     $sformatf("tl_ul_side_flash_status_q[i=%0d]=0x%0x",
                                               tl_ul_side_idx,
                                               tl_ul_side_flash_status_q[tl_ul_side_idx])},
                                     UVM_DEBUG)
                    // removing all old items up to the one which made it to spi_side
                    for (int i=0; i <= tl_ul_side_idx; i++) begin
                      `uvm_info(`gfn, $sformatf("Popping 'tl_ul_side_flash_status_q[i=%0d]=0x%0x",i,
                                                tl_ul_side_flash_status_q[0]), UVM_DEBUG)
                      void'(tl_ul_side_flash_status_q.pop_front());
                    end
                  end // if (tl_ul_side_idx != -1)
                  else if (tl_ul_fuzzy_idx != -1) begin
                    if (ongoing_read_status_cmd) begin
                      // If there's a READ_STATUS flash command on-flight - we update spi_side
                      // status in task: process_tl2spi_updates
                      update_spi_side_flash_status_after_read_status = 1;
                      `uvm_info(`gfn, {"Set 'update_spi_side_flash_status_after_read_status'",
                                       "-> Update after READ_STATUS command "},
                                UVM_DEBUG)
                    end
                    else begin
                      // Note: we don't pop out tl_ul_fuzzy_flash_status_q since it's a 1-2 item
                      // queue which gets overriden on the next flash_status write
                      flash_status_q.push_back(tl_ul_fuzzy_flash_status_q[tl_ul_fuzzy_idx]);
                      `uvm_info(`gfn, {"The RTL committed value is found in ",
                                       $sformatf("tl_ul_fuzzy_flash_status_q[i=%0d]=0x%0x",
                                                 tl_ul_fuzzy_idx,
                                                 tl_ul_fuzzy_flash_status_q[tl_ul_fuzzy_idx])},
                                UVM_DEBUG)
                    end
                  end // if (tl_ul_fuzzy_idx != -1)

                  // Predicted queues non-empty and value committed ? -> we update spi_side_flash_status
                  if (flash_status_q.size > 0) begin
                    // Just for easier readability of the comparison
                    flash_status_t flash_rtl_committed;
                    bit tweak_wel_busy;
                    // 8th SCK clk (byte beat) and we update SPI side
                    `uvm_info(`gfn, {"Updating the SPI-side. Old spi-side flash_status value:",
                                     $sformatf(" 0x%0x",spi_side_flash_status)}, UVM_DEBUG)

                    // Updating SPI-side with committed value:
                    spi_side_flash_status = flash_status_q[0];
                    flash_rtl_committed = f_status_rtl_committed_value;

                    // We check if the current committed value is the newest write, if there was a
                    // previous write which clared WEL/BUSY, clear them (upon checking on actual RTL
                    // value)!

                    if (tl_ul_side_idx != -1 && tl_ul_fuzzy_idx > 0) begin
                      flash_status_t predicted_flash = flash_status_q[0];
                      // Item found in 'tl_ul_fuzzy_flash_status_q'

                      // Check value RTL has comitted at this point, because it can happen
                      // there have been 1+ writes and the 2nd write gets picked-up for
                      // 'other_status' bits, but maybe WEL/BUSY are different
                      if ( (flash_rtl_committed.wel != predicted_flash.wel) ||
                           (flash_rtl_committed.busy != predicted_flash.busy) ) begin
                        tweak_wel_busy = 1;
                      end

                    end // if (tl_ul_side_idx != -1 && tl_ul_fuzzy_idx > 0)
                    else if (tl_ul_side_idx == -1 && (tl_ul_fuzzy_idx >= 0) &&
                             tl_ul_fuzzy_flash_status_q.size > 1) begin
                      flash_status_t predicted_flash = tl_ul_fuzzy_flash_status_q[tl_ul_fuzzy_idx];

                      // Other_status bits matched (in function 'flash_sts_committed_in_q',
                      // but not WEL OR busy: It can happen the WEL/busy bit had been clear by a
                      // previous write
                      if ( (flash_rtl_committed.wel != predicted_flash.wel) ||
                          (flash_rtl_committed.busy != predicted_flash.busy) ) begin
                        tweak_wel_busy = 1;
                      end
                    end // if (tl_ul_side_idx == -1 && (tl_ul_fuzzy_idx > 0) &&...

                    // Ammend BUSY/WEL depending on the written flash_status:
                    if (tweak_wel_busy) begin
                      // We check the value the RTL has comitted at this point, because it can happen
                      // there have been 1+ writes and the 2nd write gets picked-up
                      if (flash_rtl_committed.wel != spi_side_flash_status.wel &&
                          // Wel was cleared in the previous write - just the value hadn't update
                          tl_ul_fuzzy_flash_status_q[0].wel == flash_rtl_committed.wel) begin
                        // WEL adjustment
                        `uvm_info(`gfn, $sformatf("%s WEL since it had previously been cleared",
                                                  tl_ul_fuzzy_flash_status_q[0].wel ? "Setting" :
                                                  "Clearing"), UVM_DEBUG)
                        spi_side_flash_status.wel = tl_ul_fuzzy_flash_status_q[0].wel;
                      end

                      if (flash_rtl_committed.busy != spi_side_flash_status.busy &&
                          // Busy was cleared in the previous write - just the value hadn't update
                          tl_ul_fuzzy_flash_status_q[0].busy == flash_rtl_committed.busy) begin
                        // Busy adjustment
                        `uvm_info(`gfn, $sformatf("%s BUSY since it had previously been cleared",
                                                  tl_ul_fuzzy_flash_status_q[0].busy ? "Setting" :
                                                  "Clearing"), UVM_DEBUG)
                        spi_side_flash_status.busy = tl_ul_fuzzy_flash_status_q[0].busy;
                      end
                    end // if (tweak_wel_busy)


                    // We need to tweak the predicted Qs busy and WEL bits in order to keep our
                    // predictions up to date. Here they update on each spi beat byte.
                    tweak_busy_wel_in_q(spi_side_flash_status.wel, spi_side_flash_status.busy,
                                        "tl_ul_side_flash_status_q", tl_ul_side_flash_status_q);
                    tweak_busy_wel_in_q(spi_side_flash_status.wel, spi_side_flash_status.busy,
                                        "tl_ul_fuzzy_flash_status_q", tl_ul_fuzzy_flash_status_q);
                    `uvm_info(`gfn,
                              $sformatf("Updating the SPI-side of flash_status to: 0x%0x",
                                        spi_side_flash_status), UVM_DEBUG)

                  end // if (flash_status_q.size > 0)
                  else if (!update_spi_side_flash_status_after_read_status) begin
                    `uvm_fatal(`gfn, "RTL flash_status committed value is not in a predicted Q")
                  end

                end // if (comitted_value_predicted)

                // event triggered after the spi_side is updated
                `uvm_info(`gfn, "Triggering event 'check_spi_status_bits_ev'", UVM_DEBUG)
                -> check_spi_status_bits_ev;
              end
            end
          join_any
          disable fork;
        end: isolation_thread
      join
      `uvm_info(`gfn, "[process_tl2spi_updates] - thread killed", UVM_DEBUG)

      // All CSR predictions here:
      `uvm_info(`gfn, "Updating TL-UL register side ", UVM_DEBUG)

      old_flash_status  = `gmv(ral.flash_status);
      `uvm_info(`gfn,
                $sformatf("Updating predicted old flash_status value to: 0x%0x",old_flash_status),
                UVM_DEBUG)

      tl_ul_old_flash_status_q.push_back(old_flash_status);
      `uvm_info(`gfn, $sformatf("Pushing 0x%0x, on 'tl_ul_old_flash_status_q'",old_flash_status),
                UVM_DEBUG)

      foreach(tl_ul_old_flash_status_q[i]) begin
        `uvm_info(`gfn, $sformatf(
                      "tl_ul_old_flash_status_q[i] = 0x%0x",tl_ul_old_flash_status_q[i]), UVM_DEBUG)
      end
      `uvm_info(`gfn, $sformatf("Up to know, 'tl_ul_old_flash_status_q' has %0d items",
                                tl_ul_old_flash_status_q.size), UVM_DEBUG)

      // tl_ul_old_flash_status_q will have up to 2 items max. That's because once CSB goes high, if
      // SW reads flash_Status we may get the "older old" flash_status or the newer "old" value
      // depending on when the read arrives
      while(tl_ul_old_flash_status_q.size > 2) begin
        `uvm_info(`gfn, $sformatf("Clearing item (0x%0x) from queue: 'tl_ul_old_flash_status_q'",
                                  tl_ul_old_flash_status_q[0] ), UVM_DEBUG)
        void'(tl_ul_old_flash_status_q.pop_front());
      end
      `uvm_info(`gfn, $sformatf("spi_side_flash_status = 0x%0x",spi_side_flash_status), UVM_DEBUG)

      // Adding a 25%clk_cycle delay to make sure if the command is passthrough the correct "busy"
      // value will be read. This delay is neccessary since the thread that handles passthrough
      // already has a 1ps delay
      #(cfg.spi_host_agent_cfg.sck_period_ps/4 * 1ps);

      // Update flash_status predicted value
      `DV_CHECK_EQ_FATAL( ral.flash_status.predict(.value(spi_side_flash_status),
                                                   .kind(UVM_PREDICT_READ)), 1,
                          "ral.flash_status.predict did not succeed")
      `uvm_info(`gfn, $sformatf("Updated TL-UL flash_status CSR to: spi_side_flash_status=0x%0x",
                                  spi_side_flash_status), UVM_DEBUG)

      // We need to tweak the predicted Qs busy and WEL bits in order to keep our
      // predictions up to date. Here they update at the end of the transaction.
      tweak_busy_wel_in_q(spi_side_flash_status.wel, spi_side_flash_status.busy,
                          "tl_ul_side_flash_status_q", tl_ul_side_flash_status_q);


      tweak_busy_wel_in_q(spi_side_flash_status.wel, spi_side_flash_status.busy,
                          "tl_ul_fuzzy_flash_status_q", tl_ul_fuzzy_flash_status_q );

      // Triggered after CSB is asserted
      -> CSB_not_active_ev;
      `uvm_info(`gfn, "Triggered 'CSB_not_active_ev'", UVM_DEBUG)

    end // forever begin
  endtask // process_tl2spi_updates

  // Tweaks busy/wel bits in predicted queues in order to keep them up to date with the latest
  // SCK/CSB values
  function void tweak_busy_wel_in_q(bit wel, bit busy,  string queue_name,
                                    ref flash_status_t  flash_status_q[$]);
    flash_status_t fs;
    foreach (flash_status_q[i]) begin
      bit tweaked;
      //          $display("flash_status_q[i] = 0x%0x",flash_status_q[i]);
      fs = flash_status_q[i];
      if ( (fs.busy != 0 && fs.busy != spi_side_flash_status.busy)) begin
        flash_status_q[i].busy = spi_side_flash_status.busy;
        tweaked = 1;
      end
      if ( (fs.wel != 0 && fs.wel != spi_side_flash_status.wel)) begin
        flash_status_q[i].wel = spi_side_flash_status.wel;
        tweaked = 1;
      end
      if (tweaked) begin
        `uvm_info(`gfn, {"Tweaking predicted flash_status due to last command setting  busy"
                         ," - ",$sformatf("OLD:%s[i]=0x%0x | NEW: %s[i]=0x%0x", queue_name, fs,
                                          queue_name, flash_status_q[i])}, UVM_DEBUG)
      end
    end // foreach (flash_status_q[i])

  endfunction


  // Receives a flash_status_t queue and returns '1' if the value has yet been comitted
  // This function is used to update spi_side_flash_status value
  // Returns 1 if the item is in the queue
  function bit flash_sts_committed_in_q(flash_status_t flash_status_q[$],
                                                  bit compare_busy, bit compare_wel,
                                                  ref int idx);
    bit             matched;
    flash_status_t  f_status_rtl_committed_value;
    f_status_rtl_committed_value = fetch_flash_status_rtl_committed_value();
    idx = -1;
    `uvm_info(`gfn, $sformatf("Comparing items in the queue: compare_busy=%0d | compare_wel = %0d",
                              compare_busy, compare_wel), UVM_DEBUG)

    foreach (flash_status_q[i]) begin
      `uvm_info(`gfn, $sformatf("flash_status_q[i=%0d] = 0x%0x", i, flash_status_q[i]), UVM_DEBUG)
      matched = (f_status_rtl_committed_value.other_status == flash_status_q[i].other_status)
        && (!compare_busy ? 1 : (f_status_rtl_committed_value.busy == flash_status_q[i].busy))
          && (!compare_wel ? 1 : (f_status_rtl_committed_value.wel == flash_status_q[i].wel));
      if (matched) begin
        idx = i;
        break;
      end
    end

    if (matched) begin
      `uvm_info(`gfn, $sformatf("Item matched - flash_status_q[idx=%0d]=0x%0x",idx,
                                flash_status_q[idx]), UVM_DEBUG)
    end
    else begin
      `uvm_info(`gfn, "No flash_status value in the queue matched the RTL committed value",
                UVM_DEBUG)
    end
    return matched;
  endfunction

  // Snoops into RTL's flash_status committed value. It's used to determine when a given value
  // crossed CDC boundaries.
  function flash_status_t fetch_flash_status_rtl_committed_value();
    uvm_hdl_data_t 	rtl_sck_status_committed_value;
    flash_status_t  fs_committed_value;
    uvm_hdl_read("tb.dut.u_spid_status.sck_status_committed", rtl_sck_status_committed_value);
    fs_committed_value = flash_status_t'(rtl_sck_status_committed_value);
    `uvm_info(`gfn, $sformatf("RTL's flash_status committed value: 0x%0x", fs_committed_value),
              UVM_DEBUG)
    return fs_committed_value;
  endfunction

  // RX a spi_txn from the monitor containing {opcode+addr} and shares it with the tasks who need it
  virtual task upstream_req_fifo_distributor();
    forever begin
      spi_item spi_txn;
      upstream_spi_req_fifo.get(spi_txn);
      `uvm_info(`gfn,$sformatf(
             "RCVD partial item {OP=0x%x,addr=%p} on 'upstream_spi_req_fifo' distributing the item"
                               , spi_txn.opcode, spi_txn.address_q), UVM_DEBUG)

      process_read_status_cmd(spi_txn);
      process_read_buffer_cmd(spi_txn);
    end
  endtask

  // Takes the opcode+addr and if it's a status commands check the return data is correct
  virtual task process_read_status_cmd(spi_item spi_txn);
    int start_addr;
    bit [23:0] status = `gmv(ral.flash_status); // 3 bytes
    bit [7:0]  spi_read_status_bits;
    flash_status_t exp_data_q[$] = {spi_side_flash_status, tl_ul_side_flash_status_q};
    int        match;
    flash_status_t matched_flash_status;
    flash_status_t ongoing_command_fuzzy_flash_status;
    bit        ongoing_command_fuzzy_status_set;
    spi_item status_item;
    bit        ignore_busy_bit;
    internal_process_cmd_e cmd_type;
    bit        is_fuzzy_q_match;

    status_item = spi_txn;


    cmd_type    = triage_flash_cmd(status_item.opcode, ignore_busy_bit);
    if (cmd_type == InternalProcessStatus) begin
      `uvm_info(`gfn,
                $sformatf("TB received READ_STATUS command (opcode=0x%0x)",status_item.opcode),
                UVM_DEBUG)

      ongoing_read_status_cmd = 1;
      fork
        begin: isolation_thread
          fork
            begin
              // Exit if CSB becomes inactive
              wait (CSB_not_active_ev.triggered);
              `uvm_info(`gfn,
                        "[CSB_not_active_ev triggered] - CSB has gone inactive - killing thread",
                        UVM_DEBUG)
            end
            begin
              forever begin
                // TXN.byte_sampled_ev is triggered in both TPM and FLASH modes
                wait (check_spi_status_bits_ev.triggered);
                `uvm_info(`gfn, "[check_spi_status_bits_ev triggered]", UVM_DEBUG)
                // Event above triggers after the spi-side value is updated

                // task above is delay free since it's an infinite loop  within a fork...join_any
                // Adding some "SPI-side" clk_delay to ensure the triggering events are noticed
                #(cfg.spi_host_agent_cfg.sck_period_ps/4 * 1ps);

                if (status_item.payload_q.size==0) begin
                  // This may be the event triggered after the opcode or address
                  // We skip any comparison because the RTL hasn't output any status bits yet
                  continue;
                end


                exp_data_q = {spi_side_flash_status};

                // The value of the status register can change in the middle of SPI transactions.
                // The SPI domain updates its values every 8 clocks. However, the SW / SYS domain
                // only updates on CSB de-assertion, with the sampling point delayed by the CSB
                // edge detector. In addition, the read commands don't rotate through the registers.

                `uvm_info(`gfn,
                          $sformatf("Checking SPI status read value for opcode=0x%0x",
                                    status_item.opcode), UVM_DEBUG)
                `uvm_info(`gfn, {"Flash_status CSR value per-byte: ",$sformatf(
                                 "#0:0x%0x, #1:0x%0x, #2:0x%0x", status[7:0], status[15:8],
                                 status[23:16])}, UVM_DEBUG)

                spi_read_status_bits = status_item.payload_q[$];
                `uvm_info(`gfn, {$sformatf("[READ_STATUS - 0x%0x] ",status_item.opcode),
                                 $sformatf("RTL returned status_bits: 0x%0x (byte_number=%0d)",
                                           spi_read_status_bits, status_item.payload_q.size)},
                          UVM_DEBUG)
                `uvm_info(`gfn, {$sformatf("[READ_STATUS - 0x%0x] ", status_item.opcode),
                                 $sformatf("TB predicts spi_side_flash_status: 0x%0x",
                                           spi_side_flash_status )}, UVM_DEBUG)

                if (tl_ul_fuzzy_flash_status_q.size > 0 && spi_side_fuzzy_flash_status_q.size > 0 &&
                    update_spi_side_flash_status_after_read_status) begin

                  if (spi_side_fuzzy_flash_status_q[0] != tl_ul_fuzzy_flash_status_q[0]) begin
                    // It could happen 2 TL-UL flash_status writes occur very close in time, in
                    // which case, the RTL may output the first write as a response to a
                    // READ_STATUS command and then output the second write. In that case,
                    // spi_side_flash_status nor spi_side_fuzzy_flash_status_q won't be updated
                    // and we need to look at 'ongoing_command_fuzzy_flash_status'
                    ongoing_command_fuzzy_flash_status = tl_ul_fuzzy_flash_status_q[0];
                    ongoing_command_fuzzy_status_set = 1;
                  end
                end // if (tl_ul_fuzzy_flash_status_q.size > 0 && spi_side_fuzzy_flash_status_q.size > 0 &&...

                case (status_item.opcode)
                  READ_STATUS_1: begin
                    if (spi_side_flash_status.wel != spi_read_status_bits[1]) begin
                      // The value isn't the predicted one, is the fuzzy queue empty?
                      is_fuzzy_q_match = spi_side_fuzzy_flash_status_q.size==0 ? 0 :
                                         (spi_side_fuzzy_flash_status_q[0].wel ==
                                          spi_read_status_bits[1]);

                      if (!is_fuzzy_q_match && ongoing_command_fuzzy_status_set &&
                          ongoing_command_fuzzy_flash_status.wel == spi_read_status_bits[1] ) begin
                        is_fuzzy_q_match                                        = 1;
                        `uvm_info(`gfn, {"Setting 'is_fuzzy_q_match' because the RTL returned a",
                                         "flash_status value written before the latest write ",
                                         "(most likely there's been 2 close in time TL-UL ",
                                         "flash_status writes"}, UVM_DEBUG)
                      end

                      if (!is_fuzzy_q_match) begin
                        `uvm_error(`gfn, {$sformatf("WEL mismatch: act=0x%0x, pred_fuzzy_q (%p)",
                                          spi_read_status_bits[1], spi_side_fuzzy_flash_status_q),
                                          $sformatf(" pred=0x%0x",spi_side_flash_status.wel)})
                      end
                    end
                    if (spi_side_flash_status.busy != spi_read_status_bits[0]) begin
                      is_fuzzy_q_match = spi_side_fuzzy_flash_status_q.size==0 ? 0 :
                                         (spi_side_fuzzy_flash_status_q[0].busy ==
                                          spi_read_status_bits[0]);

                      if (!is_fuzzy_q_match && ongoing_command_fuzzy_status_set &&
                          ongoing_command_fuzzy_flash_status.busy == spi_read_status_bits[0] ) begin
                        is_fuzzy_q_match                                        = 1;
                        `uvm_info(`gfn, {"Setting 'is_fuzzy_q_match' because the RTL returned a",
                                         "flash_status value written before the latest write ",
                                         "(most likely there's been 2 close in time TL-UL ",
                                         "flash_status writes"}, UVM_DEBUG)
                      end

                      if (!is_fuzzy_q_match) begin
                        `uvm_error(`gfn, {$sformatf("BUSY mismatch: act=0x%0x, pred_fuzzy_q (%p) ",
                                          spi_read_status_bits[0], spi_side_fuzzy_flash_status_q),
                                          $sformatf("pred=0x%0x", spi_side_flash_status.busy)})
                      end
                    end
                    if (spi_side_flash_status.other_status[5:0] != spi_read_status_bits[7:2]) begin
                      is_fuzzy_q_match = spi_side_fuzzy_flash_status_q.size==0 ? 0 :
                                         (spi_side_fuzzy_flash_status_q[0].other_status[5:0] ==
                                          spi_read_status_bits[7:2]);

                      if (!is_fuzzy_q_match && ongoing_command_fuzzy_status_set &&
                          (ongoing_command_fuzzy_flash_status.other_status[5:0] ==
                           spi_read_status_bits[7:2]) ) begin
                        is_fuzzy_q_match                                        = 1;
                        `uvm_info(`gfn, {"Setting 'is_fuzzy_q_match' because the RTL returned a",
                                         "flash_status value written before the latest write ",
                                         "(most likely there's been 2 close in time TL-UL ",
                                         "flash_status writes"}, UVM_DEBUG)
                      end

                      if (!is_fuzzy_q_match) begin
                        `uvm_error(`gfn, {$sformatf("STATUS#1 other bits mismatch: {pred (0x%0x)",
                                                   spi_side_flash_status.other_status[5:0]),
                                          $sformatf(" pred_fuzzy_q (%p) , act (0x%0x)}",
                                                   spi_side_fuzzy_flash_status_q,
                                                   spi_read_status_bits[7:2])})
                      end
                    end
                    start_addr = 0;
                  end
                  READ_STATUS_2: begin
                    start_addr                                = 1;
                    if (spi_side_flash_status.other_status[13:6] !=
                       spi_read_status_bits[7:0]) begin
                      // The value isn't the predicted one, is the fuzzy queue empty?
                      is_fuzzy_q_match = spi_side_fuzzy_flash_status_q.size==0 ? 0 :
                                         (spi_side_fuzzy_flash_status_q[0].other_status[13:6] ==
                                          spi_read_status_bits[7:0]);
                      if (!is_fuzzy_q_match && ongoing_command_fuzzy_status_set &&
                          (ongoing_command_fuzzy_flash_status.other_status[13:6] ==
                           spi_read_status_bits[7:0]) ) begin
                        is_fuzzy_q_match                                        = 1;
                        `uvm_info(`gfn, {"Setting 'is_fuzzy_q_match' because the RTL returned a",
                                         " READ_STATUS which was written before the latest write ",
                                         "(most likely there's been 2 close in time TL-UL ",
                                         "flash_status writes"}, UVM_DEBUG)
                      end

                      if (!is_fuzzy_q_match) begin
                        `uvm_error(`gfn, {$sformatf("STATUS#2 other bits mismatch: {pred (0x%0x), ",
                                          spi_side_flash_status.other_status[13:6]),
                                          $sformatf("pred_fuzzy_q (%p), act (0x%0x)}",
                                          spi_side_fuzzy_flash_status_q,spi_read_status_bits[7:0])})
                      end
                    end
                  end
                  READ_STATUS_3: begin
                    start_addr                                = 2;
                    if (spi_side_flash_status.other_status[21:14] !=
                       spi_read_status_bits[7:0]) begin

                      // The value isn't the predicted one, is the fuzzy queue empty?
                      is_fuzzy_q_match = spi_side_fuzzy_flash_status_q.size==0 ? 0 :
                                         (spi_side_fuzzy_flash_status_q[0].other_status[21:14] ==
                                          spi_read_status_bits[7:0]);

                      if (!is_fuzzy_q_match && ongoing_command_fuzzy_status_set &&
                          (ongoing_command_fuzzy_flash_status.other_status[21:14] ==
                           spi_read_status_bits[7:0]) ) begin
                        is_fuzzy_q_match                                        = 1;
                        `uvm_info(`gfn, {"Setting 'is_fuzzy_q_match' because the RTL returned a",
                                         " READ_STATUS which was written before the latest write ",
                                         "(most likely there's been 2 close in time TL-UL ",
                                         "flash_status writes"}, UVM_DEBUG)
                      end


                      if (!is_fuzzy_q_match) begin
                        `uvm_error(`gfn, {$sformatf("STATUS#2 other bits mismatch: {pred (0x%0x), ",
                                          spi_side_flash_status.other_status[21:14]),
                                          $sformatf("pred_fuzzy_q (%p), act (0x%0x)}",
                                          spi_side_fuzzy_flash_status_q,spi_read_status_bits[7:0])})
                      end
                    end
                  end
                  default: begin
                    `uvm_error(`gfn, $sformatf("unexpected status opcode: 0x%0h",
                                               status_item.opcode))
                  end
                endcase

                `uvm_info(`gfn, $sformatf("Read status bits[%d:%0d] (READ_STATUS#%0d)",
                                          (8+start_addr * 8), start_addr * 8, start_addr+1),
                          UVM_DEBUG)

                matched_flash_status = is_fuzzy_q_match ? spi_side_fuzzy_flash_status_q[0] :
                                       spi_side_flash_status;
                if (spi_side_fuzzy_flash_status_q.size>0 && is_fuzzy_q_match) begin
                  `uvm_info(`gfn, {"Copying fuzzy-matched value 'spi_side_fuzzy_flash_status_q[0]'",
                                   " to 'spi_side_flash_status'"}, UVM_DEBUG)
                  spi_side_flash_status = matched_flash_status;
                  spi_side_fuzzy_flash_status_q = {};
                `uvm_info(`gfn, "'spi_side_fuzzy_flash_status_q' has been cleared", UVM_DEBUG)
              end

                if (cfg.en_cov) begin
                  // TODO: FCOV needed to add extra insight of different states in which
                  // flash_status is checked (e.g, single beat SPI txn,
                  // multi-beat READ_STATUS command, Command with no data, ...)
                  cov.flash_status_cg.sample(.status(matched_flash_status), .is_host_read(1),
                                             .sw_read_while_csb_active(0));
                end


              end
            end
          join_any
          disable fork;
        end: isolation_thread
      join

      ongoing_read_status_cmd = 0;
      `uvm_info(`gfn, "[process_read_status_cmd] - thread killed", UVM_DEBUG)

    end // if (cmd_type == InternalProcessStatus)
  endtask

  // read buffer cmd is handled separately as we can't wait until the item is completed.
  // while upstream reads the buffer, SW may prepare the data on the other side of the buffer.
  // when the item completes, the buffer may be overwritten with other data
  virtual task process_read_buffer_cmd(spi_item spi_txn);
    spi_item item;
    uint payload_idx;
    bit [31:0] start_addr, offset, read_buffer_addr;
    event      interrupt_update_ev;
    bit        reading_readbuffer=1;
    bit        predict_interrupts=0;
    item = spi_txn;

    if (cfg.spi_host_agent_cfg.spi_func_mode == SpiModeTpm) begin
      bit [TPM_ADDR_WIDTH-1:0] addr = convert_addr_from_byte_queue(item.address_q);
      // comparison is done when the item is transfered completedly
      bit [TL_DW-1:0]          ignored_returned_q[$];
      // Write commands trigger interrupts when the item is transferred
      // completely. Return-by-hw reads don't trigger interrupts.
      if (!item.write_command && !is_tpm_reg(addr, item.read_size, ignored_returned_q)) begin
        update_pending_intr_w_delay(TpmHeaderNotEmpty);
      end
    end else if (!cfg.is_read_buffer_cmd(item)) begin
      `uvm_info(`gfn, "Not a read buffer command!", UVM_DEBUG)
    end
    else begin
      `uvm_info(`gfn, "Process read buffer command", UVM_DEBUG)
      //Unsetting read buffer command tracking variables
      read_pipeline_ongoing_read_buffer_cmd  = 0;
      last_read_buffer_addr         = 0;
      readbuf_int_predicted_already = 0;
      readwatermark_int_predicted_already = 0;


      fork begin
        wait (spi_txn.dummy_cycles_ev.triggered);
        // Needs to be set here after dummy_cycles  in case the read_pipeline is enabled and the
        // threshold is crossed shortly after the starting address
        last_readbuf_intr_update_spi_clk_cycle = cfg.spi_host_agent_cfg.vif.clk_cycle;
        `uvm_info(`gfn, $sformatf("Updating last_readbuf_intr_update_spi_clk_cycle=%0d now",
                                  last_readbuf_intr_update_spi_clk_cycle), UVM_DEBUG)
      end join_none

      start_addr = convert_addr_from_byte_queue(item.address_q);


      // Use fork...join_none and lock until we return from 'compare_mem_byte' below.
      // This needs to be separated because thread below would be killed on
      // 'item.mon_item_complete=1' which occurs the moment CSB transitions 0->1.
      // If there was a read-buffer interrupt which occurred shortly before CSB=1
      // the DV_SPINWAIT could kill the thread (depends on timing), without update
      // to the interrupt predictions.
      fork begin
        `uvm_info(`gfn, "Blocking on SV event 'interrupt_update_ev'", UVM_DEBUG)
        wait (interrupt_update_ev.triggered);

        while (reading_readbuffer || (item.payload_q.size == 0 && predict_interrupts)) begin
          `uvm_info(`gfn,
                    $sformatf("'interrupt_update_ev' event is triggered (buffer_addr=0x%0x)",
                              read_buffer_addr + 1 ), UVM_DEBUG)
          last_readbuf_intr_update_spi_clk_cycle = cfg.spi_host_agent_cfg.vif.clk_cycle;
          last_read_buffer_addr = read_buffer_addr + 1;
          `uvm_info(`gfn, {$sformatf("Reading read-buffer:\n start_addr=0x%0x\n ",start_addr),
                           $sformatf("last_read_buffer_addr=0x%0x\n ",last_read_buffer_addr)},
                    UVM_DEBUG)
          if (start_addr == read_buffer_addr /*&& start_addr % READ_BUFFER_HALF_SIZE == 0*/) begin
            // Also predicting the first address, in case the starting addrcauses any flip/watermark
            // interrupt
            predict_read_buffer_intr(read_buffer_addr, item.opcode, item.read_pipeline_mode>0);
          end
          predict_read_buffer_intr(read_buffer_addr + 1, item.opcode, item.read_pipeline_mode>0);

          // task above is delay free since it's within a fork...join_any
          // Adding some "SPI-side" clk_delay to ensure the triggering events are noticed
          #(cfg.spi_host_agent_cfg.sck_period_ps/2 * 1ps);

          if(item.payload_q.size == 0 && predict_interrupts) begin
            // Transaction finished exiting:
            predict_interrupts = 0;
            `uvm_info(`gfn, "Exiting the readbuf/watermark interrupt prediction loop", UVM_DEBUG)
            break;
          end
          `uvm_info(`gfn, "Blocking on SV event 'interrupt_update_ev'", UVM_DEBUG)
          wait (interrupt_update_ev.triggered);
        end
        `uvm_info(`gfn, "Exiting interrupt update fork", UVM_DEBUG)
      end join_none


      //Initialise here in case command is cancelled and no payload is read
      read_buffer_addr = start_addr + payload_idx;
      read_pipeline_ongoing_read_buffer_cmd = item.read_pipeline_mode>0 ? 1: 0;

      `DV_SPINWAIT(
        while (1) begin
          wait (item.payload_q.size > payload_idx || item.mon_item_complete);
          if (item.payload_q.size > payload_idx) begin
            ongoing_read_buffer_cmd = 1;

            offset = (start_addr + payload_idx) % READ_BUFFER_SIZE;
            `uvm_info(`gfn, $sformatf("Comparing memory addr -> base=0x%0x + offset=0x%0x",
                                      READ_BUFFER_START_ADDR, offset), UVM_DEBUG)

            compare_mem_byte(READ_BUFFER_START_ADDR, offset, item.payload_q[payload_idx],
                             payload_idx, "Read buffer");
            `uvm_info(`gfn, $sformatf("Comparison complete for -> base=0x%0x + offset=0x%0x",
                                      READ_BUFFER_START_ADDR, offset), UVM_DEBUG)

            read_buffer_addr = start_addr + payload_idx; // it's kept until reset
            payload_idx++; // clear to 0 when transaction is done
            -> interrupt_update_ev;
            `uvm_info(`gfn,
             $sformatf("Triggering 'interrupt_update_ev' event  (buffer_addr=0x%0x)",
                       read_buffer_addr + 1 ), UVM_DEBUG)

            `DV_CHECK_EQ(item.payload_q.size, payload_idx)
          end
          if (item.mon_item_complete) begin
            `uvm_info(`gfn,
             "item.mon_item_complete=1 -> disabling all threads under DV_SPINWAIT", UVM_DEBUG)
            break;
          end
        end
        , // while(1)
        "timeout occurred when reading read buffer!",//default message
        default_spinwait_timeout_ns*4//, // Increase the default timeout by 4 since the
                                         // payload_size can be up to 3000 bytes based
                                         // on sequence constraints
      )


      //Exiting while loop after we finish reading the buffer and triggering the event
      //  in case the process is waiting - so we unlock it
      read_pipeline_read_buffer_cmd_last = read_pipeline_ongoing_read_buffer_cmd;
      read_pipeline_ongoing_read_buffer_cmd = 0;
      ongoing_read_buffer_cmd = 0;
      if (item.payload_q.size == 0 && start_addr == read_buffer_addr)
        predict_interrupts = 1;
      reading_readbuffer = 0;
      -> interrupt_update_ev;

      if(item.payload_q.size == 0) begin
        last_read_cmd_no_payload = 1;
        // No payload, hence the start address was never read. Setting to old last_read_addr
        read_buffer_addr = `gmv(ral.last_read_addr);
        if (item.read_pipeline_mode > 0 && item.opcode inside {READ_QUAD,READ_QUADIO }) begin
          // setting here, in case the CMd doesn't have any payload , the RTL will have already
          // fetched from memory In some cases, depending on the start_addr that may trigger a
          // readbufflip/readwatermark interrupt when the read pipeline is enabled
          last_read_buffer_addr = start_addr;
        end
      end

      // Only update when it has payload OR
      // When Incomplete read command, but RTL has already fetched data and some of it it's in
      // the read pipeline. In addition, start_addr must be different to prior recorded address
      // otherwise the update won't happen
      if ((payload_idx > 0) || (start_addr != `gmv(ral.last_read_addr) &&
         (item.read_pipeline_mode > 0) && payload_idx==0 && item.read_size==0)) begin
        bit updating_last_read_addr=1;
        if(item.read_pipeline_mode > 0 && item.opcode inside {READ_QUAD, READ_QUADIO }) begin
          string print_str =
                           "Opcode is inside {READ_QUAD, READ_QUADIO} and read_pipeline is enabled";
          print_str = {print_str, ".\n", "The RTL believes the read_addr is 1 unit above because",
                       " the data has been read and is already in the read_pipeline, it has just",
                       " not  come out to the host yet. Hence we increase read_buffer_addr by 1"};
          `uvm_info(`gfn, print_str,
                    UVM_DEBUG)
          read_buffer_addr++;
        end // if (payload_idx>0 && item.read_pipeline_mode > 0...
        else if (item.terminated_before_read_pipeline) begin
          // SPI Txn was terminated before the dummy cycles/read_pipeline started, hence the RTL
          // didn't even fetch the first address
          updating_last_read_addr = 0;
        end

        if (updating_last_read_addr) begin
          // Update read_buffer_addr predicted value
          `DV_CHECK_EQ_FATAL( ral.last_read_addr.predict(.value(read_buffer_addr),
                                                         .kind(UVM_PREDICT_READ)), 1,
                              "ral.last_read_addr.predict did not succeed")
          `uvm_info(`gfn, $sformatf("Update last_read_addr to 0x%0x", read_buffer_addr), UVM_MEDIUM)

        end
        else begin
          `uvm_info(`gfn, {"Not updating 'last_read_addr' since the spi txn was cancelled before ",
                           "the RTL fetched any data"}, UVM_DEBUG)
        end
      end
    end
  endtask // process_read_buffer_cmd

  virtual function void predict_read_buffer_intr(int addr, bit [7:0] opcode,
                                                 bit read_pipeline_enabled);
    int threshold = `gmv(ral.read_threshold);
    int offset;
    bit watermark_crossed_initial_addr, buf_flip_crossed_initial_addr;

    if(read_pipeline_enabled) begin
      if(opcode inside {READ_CMD_LIST} /*&& !(opcode inside {READ_NORMAL,READ_FAST})*/) begin

        offset                              = addr % READ_BUFFER_HALF_SIZE;
        if (offset >= threshold && threshold > 0 && !read_buffer_watermark_triggered) begin
          //covers the case when the original address crosses the watermark, but the next one doesn't because it wraps
          `uvm_info(`gfn, "Read-pipeline ON -> 1st addr crossed watermark interrupt threshold",
                    UVM_DEBUG)
          watermark_crossed_initial_addr = 1;
        end
        if (addr > 0 &&
            addr % READ_BUFFER_HALF_SIZE == 0) begin
          `uvm_info(`gfn, "Read-pipeline ON -> 1st addr crossed buf_flip interrupt threshold",
                    UVM_DEBUG)
          buf_flip_crossed_initial_addr  = 1;
        end

        // If the read_pipeline feature is enabled, that means the RTL will be "ahead" with data
        // from the read buffer stored in the internal read_pipeline
        `uvm_info(`gfn , "Increasing read buffer address because read_pipeline is ON", UVM_DEBUG)
        addr++;
      end
    end
    offset                              = addr % READ_BUFFER_HALF_SIZE;

    `uvm_info(`gfn, {$sformatf("Read-buffer command (op=0x%0x) - addr=0x%0x - offset=0x%0x",
                              opcode, addr, offset),
                     $sformatf(" - threshold=0x%0x - watermark_crossed_initial_addr=0x%0x",
                               threshold, watermark_crossed_initial_addr),
                     $sformatf(" - buf_flip_crossed_initial_addr=0x%0x",
                               buf_flip_crossed_initial_addr),
                     $sformatf(" - read_buffer_watermark_triggered=0x%0x",
                               read_buffer_watermark_triggered),
                     $sformatf(" - READ_BUFFER_HALF_SIZE=0x%0x",READ_BUFFER_HALF_SIZE)}

              , UVM_DEBUG)

    if (watermark_crossed_initial_addr ||
        (offset >= threshold && threshold > 0 && !read_buffer_watermark_triggered)) begin
      read_buffer_watermark_triggered = 1;
      update_pending_intr_w_delay(ReadbufWatermark);
      `uvm_info(`gfn, $sformatf("read buffer watermark is triggered, addr: 0x%0x", addr),
                UVM_MEDIUM)
    end
    if (buf_flip_crossed_initial_addr ||
        (addr>0 && addr % READ_BUFFER_HALF_SIZE == 0)) begin
      // after flip, WM can be triggered again
      read_buffer_watermark_triggered = 0;
      update_pending_intr_w_delay(ReadbufFlip);
      `uvm_info(`gfn, $sformatf("read buffer flip is triggered, addr: 0x%0x", addr),
                UVM_MEDIUM)
      if (cfg.en_cov) begin
        // flip at full buffer size or half
        bit flip_position = addr % READ_BUFFER_SIZE == 0;
        cov.spi_device_buffer_boundary_cg.sample(opcode, flip_position);
      end
    end
  endfunction

  // flash/tpm interrupt is updated from spi domain to sys clk domain, which takes 2+ cycles.
  // allow the 1st interrupt read doesn't aligned with the exp value, but if SW issues 2 interrupt
  // read with no delay, the 2nd one may also doesn't match.
  // add some cycle delays to make it close to design behavior, so that the 2nd interrupt read
  // must match.
  virtual function void update_pending_intr_w_delay(spi_device_intr_e intr, int delay_cyc = 4);
    fork
      begin
        `uvm_info(`gfn,
                  $sformatf("Wait %0d cycles to enable compare of %s interrupt",delay_cyc, intr.name()),
                  UVM_MEDIUM)
        //Adding a SPI clock cycle
        //        #(cfg.spi_host_agent_cfg.sck_period_ps * 1ps);

        intr_pending_set_after_delay[intr]=1;

        cfg.clk_rst_vif.wait_n_clks(delay_cyc);
        `uvm_info(`gfn,$sformatf("Wait done; Enable compare of %s", intr.name()), UVM_MEDIUM)
        if(intr_pending_read_set_before_delay[intr]) begin
          string print_str = $sformatf("%s interrupt already predicted and read on TL-UL side",
                                       intr.name());
          print_str = {print_str, " ",
                  $sformatf("Unsetting from 'intr_pending_read_set_before_delay[%s]'",intr.name())};
          `uvm_info(`gfn, print_str, UVM_DEBUG)
          intr_pending_read_set_before_delay[intr] = 0;
        end
        else if((intr == ReadbufFlip && readbuf_int_predicted_already) ||
                (intr == ReadbufWatermark && readwatermark_int_predicted_already)
                ) begin
          if(intr == ReadbufFlip) begin
            string print_str = "Readbuf_flip already predicted. Don't set it again - unsetting";
            print_str = {print_str, " ",
                         "'readbuf_int_predicted_already' and intr_pending_set_after_delay[intr]"};
            readbuf_int_predicted_already = 0;
            intr_pending_set_after_delay[intr] = 0;

            `uvm_info(`gfn, print_str, UVM_DEBUG)
          end

          if(intr == ReadbufWatermark) begin
            string print_str ="Readbuf_watermark already predicted. Don't set it again - unsetting";
            print_str = {print_str, " ",
                    "'readwatermark_int_predicted_already' and intr_pending_set_after_delay[intr]"};
            readwatermark_int_predicted_already = 0;
            intr_pending_set_after_delay[intr] = 0;
            `uvm_info(`gfn, print_str, UVM_DEBUG)
          end

        end
        else begin
          intr_trigger_pending[intr] = 1;
          `uvm_info(`gfn, $sformatf("Setting 'intr_trigger_pending[intr=%s]",intr.name()),
                    UVM_DEBUG)
        end

        if(intr == ReadbufFlip && readbuf_int_predicted_already) begin
          readbuf_int_predicted_already = 0;
          `uvm_info(`gfn, {"Readbuf_flip already predicted. Don't set it again",
                           " - unsetting 'readbuf_int_predicted_already'"} ,UVM_DEBUG)
        end
      end // fork begin
    join_none
  endfunction // update_pending_intr_w_delay


  // process_tl_access:this task processes incoming access into the IP over tl interface
  // this is already called in cip_base_scoreboard::process_tl_a/d_chan_fifo tasks
  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
    bit     do_read_check   = 1'b0; // TODO: fixme
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end
    else if (csr_addr inside {[cfg.sram_egress_start_addr:cfg.sram_egress_end_addr]}) begin
      // TODO: Anything to do here?
      return;
    end
    else if (csr_addr inside {[cfg.sram_ingress_start_addr:cfg.sram_ingress_end_addr]}) begin
      if (!write) begin
        // cip_base_scoreboard compares the mem read only when the address exists
        // just need to ensure address exists here and mem check is done at process_mem_read
        `DV_CHECK(spi_mem.addr_exists(csr_addr))
      end
      return;
    end
    else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    `uvm_info(`gfn,$sformatf(
    "TL-UL txn: [channel=%p] - {addr=0x%0x, a_size=d'%0d, a_mask=0x%0x, is_write=d'%0d, data=0x%0x",
                  channel,item.a_addr, item.a_size, item.a_mask, write,
                  write ? item.a_data : item.d_data),
              UVM_DEBUG)

    `uvm_info(`gfn, $sformatf("CSR name: %s",csr.get_name()), UVM_DEBUG)
    // if incoming access is a write to a valid csr, then make updates right away
    // don't update flash_status predict value as it's updated at the end of spi transaction
    if (write && channel == AddrChannel && csr.get_name != "flash_status") begin
      // store the previous value if it's a TPM HW reg and SPI interface is busy
      if (!cfg.spi_host_agent_cfg.vif.csb[TPM_CSB_ID] &&
          csr.get_name inside {ALL_TPM_HW_REG_NAMES}) begin
        // the value of TPM_ACCESS_0-3 is in the CSR tpm_access_0
        // TPM_ACCESS_4 is in the CSR tpm_access_1
        if (csr.get_name == "tpm_access_0") begin
          foreach(ral.tpm_access_0.access[i]) begin
            tpm_hw_reg_pre_val_aa[$sformatf("tpm_access_%0d", i)] = `gmv(ral.tpm_access_0.access[i]);
          end
        end else if (csr.get_name == "tpm_access_1") begin
          tpm_hw_reg_pre_val_aa["tpm_access_4"] = `gmv(csr);
        end else begin
          tpm_hw_reg_pre_val_aa[csr.get_name] = `gmv(csr);
        end
      end
      if (cfg.en_cov && csr.get_name == "addr_mode") begin
        bit pre_addr4b = `gmv(ral.addr_mode.addr_4b_en);
        bit cur_addr4b = get_field_val(ral.addr_mode.addr_4b_en, item.a_data);
        // cover that the addr4b is updated by SW
        if (pre_addr4b != cur_addr4b) cov.sw_update_addr4b_cg.sample();
      end
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
    end

    // process the csr req
    case (csr.get_name())
      "addr_mode": begin
        // Note: The expected behaviour is SW won't write to addr_mode whilst the host is sending
        // data. The expectation is SW will only initialise the value, then the host will handle 3
        // to 4 byte addresses bya sending EN4B EX4B flash commands.
        // EN4B/EX4B commands take precedence over TL-UL writes, so if the write collides with
        // EN4B/EX4B commands the written value will be ignored.
        // ADDR_MODE updates on SCK side after the first byte is received. The TB updates
        // ADDR_MODE.addr_4b_en at the end of the flash_command, so the TB won't need to handle this
        // case differently.
        if (write && channel == AddrChannel) begin
          bit rtl_pending;
          tl_ul_side_addr_mode_pending = 1;
          tl_ul_side_addr_mode_addr_4b_en = item.a_data[0];

          `uvm_info(`gfn, $sformatf("ADDR_MODE.addr_4b_en Write (0x%0x)",
                                    tl_ul_side_addr_mode_addr_4b_en), UVM_DEBUG)

          // Check the pending bit is set
          csr_rd(.ptr(ral.addr_mode.pending), .value(rtl_pending), .backdoor(1));
          `DV_CHECK_EQ(rtl_pending, tl_ul_side_addr_mode_pending,
                       $sformatf("Comparison mismatch, act (0x%0x) != exp %p",
                                 rtl_pending, tl_ul_side_addr_mode_pending))
        end
        if (!write && channel == DataChannel) begin
          bit [TL_DW-1:0] exp_addr_mode = tl_ul_side_addr_mode_pending ?
                                          tl_ul_side_addr_mode_addr_4b_en :
                                          spi_side_addr_mode_addr_4b_en;
          `uvm_info(`gfn, $sformatf("ADDR_MODE read: act=0x%0x, exp=0x%0x",
                                    item.d_data, exp_addr_mode), UVM_DEBUG)

          `DV_CHECK_EQ(item.d_data[0], exp_addr_mode,
                       $sformatf("Comparison mismatch [addr_4b_en], act (0x%0x) != exp %p",
                                 item.d_data[0], exp_addr_mode))

          `DV_CHECK_EQ(item.d_data[TL_DW-1], tl_ul_side_addr_mode_pending,
                       $sformatf("Comparison mismatch [pending], act (0x%0x) != exp %p",
                                 item.d_data[TL_DW-1], tl_ul_side_addr_mode_pending))
        end
      end
      "flash_status": begin
        if (write && channel == AddrChannel) begin
          flash_status_t flash_status = item.a_data;
          `uvm_info(`gfn, $sformatf("SW Write to flash_status (0x%0x)", item.a_data), UVM_DEBUG)

          // busy field is W0C. Setting to 1 has no effect
          flash_status.busy = flash_status.busy & `gmv(ral.flash_status.busy);
          flash_status.wel = flash_status.wel & `gmv(ral.flash_status.wel);

          `uvm_info(`gfn, $sformatf("TB predicts flash_status (0x%0x)", flash_status), UVM_DEBUG)

          //'tl_ul_side_flash_status_q' is picked inmediatly on every SPI byte beat.
          // Hence, we need to only push the items to the queue at the "right time"
          // in function 'populate_tl_ul_side_flash_status_q'
          populate_tl_ul_side_flash_status_q(flash_status);
        end
        if (!write && channel == DataChannel) begin
          string print_str;
          flash_status_t exp_val = `gmv(ral.flash_status); // predicted value updated when CSB (0->1)
          flash_status_t exp_data_q[$] = {tl_ul_old_flash_status_q, exp_val,
                                          tl_ul_fuzzy_flash_status_q};
          foreach(exp_data_q[i])
            print_str = {print_str, $sformatf(" exp_data_q[i=%0d] = 0x%0x",i,exp_data_q[i])};

          `uvm_info(`gfn, $sformatf(
                                    "SW Read to flash_status (0x%0x) - exp_data_q =%s",
                                    item.d_data, print_str), UVM_DEBUG)
          `uvm_info(`gfn, $sformatf(
                          "SW Read to flash_status (0x%0x) (exp_data_q.size=%0d) - exp_data_q = %p",
                                    item.d_data, exp_data_q.size, exp_data_q), UVM_DEBUG)

          // matching against predicted values?
          `DV_CHECK(item.d_data inside {exp_data_q},
                    $sformatf("act (0x%0x) != exp %p", item.d_data, exp_data_q))

          if ( (item.d_data inside {tl_ul_fuzzy_flash_status_q}) &&
               !(item.d_data inside {tl_ul_old_flash_status_q, exp_val})) begin
            // Matched the value in the 'future values' queue (tl_ul_fuzzy_flash_status_q)
            `uvm_info(`gfn, "Clearing 'tl_ul_old_flash_status_q': its values are stale", UVM_DEBUG)
            tl_ul_old_flash_status_q = {};
            tl_ul_old_flash_status_q.push_back(item.d_data);
            `uvm_info(`gfn, $sformatf("Populating 'tl_ul_old_flash_status_q' with 0x%0x",
                                      item.d_data), UVM_DEBUG)
          end

          if (tl_ul_old_flash_status_q.size > 2) begin
            `uvm_fatal(`gfn, $sformatf(
                            "'tl_ul_old_flash_status_q.size=%0d' - the max allowedvalue is 2",
                                       tl_ul_old_flash_status_q.size))
          end

          if (cfg.en_cov) begin
            cov.flash_status_cg.sample(.status(item.d_data), .is_host_read(0),
                .sw_read_while_csb_active(!cfg.spi_host_agent_cfg.vif.csb[FW_FLASH_CSB_ID]));
          end
        end
        // check is done above and predict is done after spi item completes. can return now
        return;
      end
      "intr_state": begin
        if (!write && channel == DataChannel) begin
          bit [NumSpiDevIntr-1:0] intr_exp = `gmv(csr);
          bit [TL_DW-1:0] intr_en = ral.intr_enable.get_mirrored_value();
          //Set when a read_line command is ongoing, or was ongoing last:
          bit             read_pipeline_cmd_now_or_last;
          bit             num_cycles_since_last_readbuf_intr_sck_update;
          spi_device_intr_e intr;
          `uvm_info(`gfn,
                    $sformatf("INTR_STATE: read (bus_value_read: 0x%0x)\nTB expects=0x%0x",
                              item.d_data, intr_exp ), UVM_DEBUG)

          foreach (intr_exp[i]) begin
            intr = spi_device_intr_e'(i); // cast to enum to get interrupt name
            if (cfg.en_cov) begin
              cov.intr_cg.sample(intr, intr_en[intr], intr_exp[intr]);
              cov.intr_pins_cg.sample(intr, cfg.intr_vif.pins[intr]);
            end

            if (!(i inside {ReadbufFlip, ReadbufWatermark, PayloadOverflow,
                            CmdFifoNotEmpty, PayloadNotEmpty, TpmHeaderNotEmpty}) ||
                (i == TpmHeaderNotEmpty && !cfg.en_check_tpm_not_empty_intr)) begin
              continue;
            end

            read_pipeline_cmd_now_or_last = read_pipeline_ongoing_read_buffer_cmd ||
                                         (read_pipeline_read_buffer_cmd_last &&
                                          ongoing_read_buffer_cmd==0);
            num_cycles_since_last_readbuf_intr_sck_update = cfg.spi_host_agent_cfg.vif.clk_cycle -
                                                            last_readbuf_intr_update_spi_clk_cycle;

            // For readbuf_flip/watermark, it can happen the read buffer data has been latched
            // onto the read pipeline, and even if the CSB isn't active, the RTL has read that
            // address and potentially also set the interrupt for it
            if (item.d_data[i] && read_pipeline_cmd_now_or_last &&
                // RTL set interrupt before full data was output to the host:
                (num_cycles_since_last_readbuf_intr_sck_update  < 8 ||
                // Either we received the interrupt from a read before we predicted it (because the
                // TB hasn't yet received a full byte of data, or the command didn't have a payload
                // (but some data was buffered in read_pipeline), but it had the readpipeline
                // enabled (hence the RTL may've read memory locations already) or the interrupt is
                // due at the end of the transaction and there's payload data:
                 (ongoing_read_buffer_cmd==0 && read_pipeline_read_buffer_cmd_last)) ) begin

              if(i == ReadbufFlip &&
                 ( (last_read_buffer_addr+1) % READ_BUFFER_HALF_SIZE == 0) ) begin
                `uvm_info(`gfn, $sformatf("TB predicts this interrupt (%s) 'early'", intr.name),
                          UVM_DEBUG)
                intr_trigger_pending[i] = 1;
                readbuf_int_predicted_already = 1;
                read_buffer_watermark_triggered = 0;
              end

              if ( (i == ReadbufWatermark) &&
                   //It needs to be equals in the case we predict early
                   ( ( (last_read_buffer_addr+1) % READ_BUFFER_HALF_SIZE) ==
                     `gmv(ral.read_threshold) && `gmv(ral.read_threshold) > 0) ) begin
                `uvm_info(`gfn, $sformatf("TB predicts this interrupt (%s) 'early'", intr.name),
                          UVM_DEBUG)
                intr_trigger_pending[i] = 1;
                readwatermark_int_predicted_already = 1;
                read_buffer_watermark_triggered = 1;
              end
            end // if (item.d_data[i] && read_pipeline_cmd_now_or_last &&...

            //TB is on its way to predict the interrupt, but the RTL already read the bit set
            if(intr_pending_set_after_delay[i] && item.d_data[i]) begin
              spi_device_intr_e intr = spi_device_intr_e'(i);
              intr_pending_set_after_delay[i] = 0;
              `uvm_info(`gfn, $sformatf("Unsetting intr_pending_set_after_delay[i=%s]",intr.name()),
                        UVM_DEBUG)
              intr_pending_read_set_before_delay[i] = 1;
              intr_trigger_pending[i] = 1;
            end

            if (!intr_trigger_pending[i]) begin
              `DV_CHECK_EQ(item.d_data[i], intr_exp[i],
                           $sformatf("Compare %s mismatch, act (0x%0x) != exp %p",
                           intr.name, item.d_data[i], intr_exp[i]))
            end else begin
              // there is an interrupt pending, update interrupt to 1
              // skip the check, as either 0 or 1 is fine
              if(item.d_data[i]) begin
                // We update intr_expt[i] once the RTL reports the interrupt, otherwise there's a
                // chance the TB will predict the interrupt quicker than the RTL
                intr_exp[i] = 1;
                `DV_CHECK_EQ_FATAL( csr.predict(.value(intr_exp), .kind(UVM_PREDICT_READ)), 1,
                                    $sformatf("%s.predict did not succeed", csr.get_name()))

                `uvm_info(`gfn, $sformatf("updating CSR intr_state with intr_exp[i=%0d]=%0d",i,
                                          intr_exp[i]), UVM_DEBUG)
                // clear pending interrupt
                intr_trigger_pending[i] = 0;
              end
              else begin
                spi_device_intr_e intr = spi_device_intr_e'(i);
                `uvm_info(`gfn, {"TB hasn't yet updated CSR status in spite of having predicted ",
                                 $sformatf("an interrupt for %s interrupt because the ",intr.name),
                                 "prediction was quicker than the RTL"}, UVM_DEBUG)
              end // else: !if(item.d_data[i])
            end // else: !if(!intr_trigger_pending[i])
          end // foreach (intr_exp[i])
          // Update local mirror copy of intr_exp
          intr_exp_read_mirrored = `gmv(csr);

          // skip updating predict value to d_data
          return;
        end // if (!write && channel == DataChannel)
        else if (write && channel == AddrChannel) begin
          bit [NumSpiDevIntr-1:0] intr_val = item.a_data;
          bit [NumSpiDevIntr-1:0] intr_exp = `gmv(csr);
          `uvm_info(`gfn, $sformatf("INTR_STATE: write (0x%0x)",intr_val ), UVM_DEBUG)

          foreach (intr_val[i]) begin
            spi_device_intr_e intr = spi_device_intr_e'(i);
            if (intr_val[i]) begin
              `uvm_info(`gfn, $sformatf("Clear %s", intr.name), UVM_MEDIUM)

              if(i == ReadbufFlip && intr_val[i] && readbuf_int_predicted_already) begin
                `uvm_info(`gfn, "'readbuf_int_predicted_already' is unset", UVM_DEBUG)
                readbuf_int_predicted_already = 0;
              end

              if ( (i == ReadbufWatermark) && intr_val[i] &&
                   readwatermark_int_predicted_already) begin
                `uvm_info(`gfn, "'readwatermark_int_predicted_already' is unset", UVM_DEBUG)
                readwatermark_int_predicted_already = 0;
              end

              // If intr_trigger_pending[i] is set and intr_exp_read_mirrored[i] is also set, that
              // means the TB has predicted another interrupt since last time intr_state was read.
              // But in the meantime, there's not been any intr_state.writes clearing the intr_state
              // register.
              if(intr_trigger_pending[i] && intr_exp_read_mirrored[i]) begin
                `uvm_info(`gfn, $sformatf("Unsetting 'intr_trigger_pending[i=%p]'",
                                          spi_device_intr_e'(i)) , UVM_DEBUG)
                intr_trigger_pending[i] = 0;
              end
              if(intr_exp_read_mirrored[i]) begin
                `uvm_info(`gfn, $sformatf("Unsetting 'intr_exp_read_mirrored[i=%p]'",
                                          spi_device_intr_e'(i)) , UVM_DEBUG)
                intr_exp_read_mirrored[i] = 0;
              end
            end
          end
        end
      end
      "intr_test": begin
        if (write && channel == AddrChannel) begin
          bit [TL_DW-1:0] intr_en = ral.intr_enable.get_mirrored_value();
          bit [NumSpiDevIntr-1:0] intr_val;
          intr_val = `gmv(ral.intr_state) | item.a_data;
          if (cfg.en_cov) begin
            foreach (intr_val[i]) begin
              cov.intr_test_cg.sample(i, item.a_data[i], intr_en[i], intr_val[i]);
            end
          end
        end
      end
      "control": begin
        ;
      end
      "upload_cmdfifo": begin
        if (!write && channel == DataChannel) begin
          `DV_CHECK_GT(upload_cmd_q.size, 0)
          // TODO: Check addr4b_mode, wel, and busy bits
          `DV_CHECK_EQ(item.d_data[7:0], upload_cmd_q.pop_front())
          update_cmdfifo_status();
        end
      end
      "upload_addrfifo": begin
        if (!write && channel == DataChannel) begin
          `DV_CHECK_GT(upload_addr_q.size, 0)
          `DV_CHECK_EQ(item.d_data, upload_addr_q.pop_front())
          update_addrfifo_status();
        end
      end
      "last_read_addr", "upload_status", "upload_status2": begin
        do_read_check = 1;
      end
      "tpm_cmd_addr": begin
        if (!write && channel == DataChannel) begin
          bit [7:0] cmd = get_field_val(ral.tpm_cmd_addr.cmd, item.d_data);
          bit [TPM_ADDR_WIDTH-1:0] addr = get_field_val(ral.tpm_cmd_addr.addr, item.d_data);
          spi_item tpm_item = spi_item::type_id::create("tpm_item", this);
          do_read_check = 0;

          // the size is temporarily stored in read_size even if it's a write item.
          // set read_size to 0 for write, when the item is fully collected
          `uvm_info(`gfn, $sformatf("SW received cmd: 0x%0x, addr = 0x%0x", cmd, addr), UVM_MEDIUM)
          tpm_item.read_size = cmd[TPM_CMD_DIR_BIT_POS-1:0] + 1;
          tpm_item.write_command = cmd[TPM_CMD_DIR_BIT_POS] == TPM_CMD_WRITE_BIT_VALUE;
          `DV_CHECK_FATAL(tpm_item.read_size inside {[1:MAX_TPM_SIZE]});
          for (int i = 0; i < TPM_ADDR_WIDTH_BYTE; i++) begin
            tpm_item.address_q.push_front(addr[8*i +: 8]);
          end
          if (tpm_item.write_command) begin // TPM write
            // TODO: Anything to do here?
          end else begin // TPM read
            // before we receive a new cmd for read, the previous one should be done
            `DV_CHECK_EQ_FATAL(tpm_read_sw_q.size, 0)
            tpm_read_sw_q.push_back(tpm_item);
          end
          // this is a status interrupt, clear it when it's read out.
          void'(ral.intr_state.tpm_header_not_empty.predict(.value(0), .kind(UVM_PREDICT_READ)));
        end
      end
      "tpm_read_fifo": begin
        if (write && channel == AddrChannel) begin
          uint num_bytes;
          int size_to_done;

          `DV_CHECK_EQ_FATAL(tpm_read_sw_q.size, 1)
          size_to_done = tpm_read_sw_q[0].read_size - tpm_read_sw_q[0].data.size;
          `DV_CHECK_GT(size_to_done, 0)

          if (size_to_done >= 4) begin
            num_bytes = 4;
          end else begin
            num_bytes = size_to_done;
          end
          for (int i = 0; i < num_bytes; i++) begin
            tpm_read_sw_q[0].data.push_back(item.a_data[8*i +: 8]);
          end
        end
      end
      "tpm_status": begin
        // TODO: Check whether the cmdaddr fifo should have something in it on
        // reads, and track wrfifo buffer acquisition and release.
      end
      default: begin
        // TODO the other regs
      end
    endcase

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (!write && channel == DataChannel) begin
      if (do_read_check) begin
        `DV_CHECK_EQ(item.d_data, `gmv(csr),
                    $sformatf("CSR %s compare mismatch act 0x%0x != exp 0x%0x",
                    csr.`gn, item.d_data, `gmv(csr)))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask // process_tl_access


  virtual task populate_tl_ul_side_flash_status_q(flash_status_t flash_status);
    bit csb_active = cfg.spi_host_agent_cfg.vif.csb[FW_FLASH_CSB_ID]===0;

    `uvm_info(`gfn, {$sformatf("Flash_status write (0x%0x) - Populating 'tl_ul_side_flash_status_q'"
                     ,flash_status),
                     $sformatf(". Up to know it has %0d entries", tl_ul_side_flash_status_q.size)},
                     UVM_DEBUG)

    // There are 2 directions:
    // - TL-UL to SPI -> update during ongoing SPI_TXN (byte beats -> check_spi_status_bits_ev)
    // - SPI to TL-UL -> update the moment CSB goes is high (plus some CDC crossing delay)
    // Thread is killed either after 2 SPI bytes, CSB going high, or CSB going low
    fork begin
      begin
        fork
          begin
            // If there is a READ_STATUS command on flight whils flash_status is being written, We
            // need to wait for 2 spi byte beats.
            // For the first beat, the RTL moves the TL-UL flash_status towards the spi-side,but the
            // returned value may have been already committed to the upstream spi host and after the
            // Second beat is when the RTL commits this written value to the return it to the host.
            `uvm_info(`gfn,$sformatf("Populating fuzzy Qs with flash_status = 0x%0x",flash_status),
                      UVM_DEBUG)

            // Keep written value in Fuzzy Qs since the TB won't accuretly model the CDC crossing
            if (tl_ul_fuzzy_flash_status_q.size > 0) begin
              `uvm_info(`gfn, $sformatf(
                            "tl_ul_fuzzy_flash_status_q[$] old_value= 0x%0x, and new_value = 0x%0x",
                                        tl_ul_fuzzy_flash_status_q[$], flash_status)
                        , UVM_DEBUG)
            end

            // It could happen the first write is not yet taken into the TL-UL side by the time this
            // write occurs, hence we need to store it in a queue
            tl_ul_fuzzy_flash_status_q.push_back(flash_status);
            while (tl_ul_fuzzy_flash_status_q.size > 2) begin
              `uvm_info(`gfn, {"Popping oldest_item",$sformatf(
                               "(0x%0x) from 'tl_ul_fuzzy_flash_status_q'",
                               tl_ul_fuzzy_flash_status_q[0])}, UVM_DEBUG)
              void'(tl_ul_fuzzy_flash_status_q.pop_front());
            end

            spi_side_fuzzy_flash_status_q = {flash_status};
            `uvm_info(`gfn, $sformatf("Setting 'spi_side_fuzzy_flash_status_q' to 0x%0x",
                                      flash_status), UVM_DEBUG)
            wait (check_spi_status_bits_ev.triggered);
            `uvm_info(`gfn, "first check_spi_status_bits_ev has been triggered", UVM_DEBUG)
            // Eigth of  a SPI cycle to ensure a second event is triggered for the 2nd wait
            // statement. Also to ensure this thread updates ahead of 'process_tl2spi_updates'
            // which has a 'cfg.spi_host_agent_cfg.sck_period_ps/4' delay.
            // So the 'tl_ul_side_flash_status_q' is updated in time for the value to propagate
            // towards the SPI side
            #(cfg.spi_host_agent_cfg.sck_period_ps/8 * 1ps);
            wait (check_spi_status_bits_ev.triggered);
            `uvm_info(`gfn, "second check_spi_status_bits_ev has been triggered... EXITING THREAD",
                      UVM_DEBUG)
          end
          begin
            wait (CSB_not_active_ev.triggered);
            if (csb_active) begin
              // It can happen the SPI command is less than 2-bytes, in which case we need to
              // update 'spi_side_flash_status' here
              flash_status_t 	rtl_sck_status_committed_value;



              `uvm_info(`gfn,
                        "Updating 'spi_side_flash_status' in different task due to CMD too short",
                        UVM_DEBUG)

              // Look into the RTL, and see if the value has yeet been committed. It'll depend on
              // the exact moment in which the TL-UL flash_status value was written. If it's been
              // committed, then update spi_side .
              rtl_sck_status_committed_value = fetch_flash_status_rtl_committed_value();

              if (tl_ul_fuzzy_flash_status_q.size > 0) begin
                int idx = -1; //Set to >=0 when valid
                bit          different_ral_value = 1;
                //$display("rtl_sck_status_committed_value
                foreach(tl_ul_fuzzy_flash_status_q[i]) begin
                  if (rtl_sck_status_committed_value == tl_ul_fuzzy_flash_status_q[i])
                    idx = i;

                  if (`gmv(ral.flash_status) == tl_ul_fuzzy_flash_status_q[i] && idx != -1)
                    different_ral_value                        = 0;
                end

                if ( different_ral_value && idx >=0 &&
                     rtl_sck_status_committed_value == tl_ul_fuzzy_flash_status_q[idx]) begin
                  int old_flash_status_idx = -1;
                  flash_status_t old_flash_status; // This is the value before it was committed
                  string print_str;
                  `uvm_info(`gfn, {$sformatf("old_value: spi_side_flash_status=0x%0x | ",
                                             spi_side_flash_status),
                                   $sformatf("new_value: spi_side_flash_status=0x%0x",
                                             tl_ul_fuzzy_flash_status_q[idx])}
                            , UVM_DEBUG)
                  // We need to save the old flash_status in the old flash_Status queue
                  csr_rd(.ptr(ral.flash_status), .value(old_flash_status), .backdoor(1));

                  // Clear all 'tl_ul_old_flash_status_q' entries if the RTL's flash_status value is
                  // in the queue
                  foreach(tl_ul_old_flash_status_q[i]) begin
                    if (tl_ul_old_flash_status_q[i] == old_flash_status)
                      old_flash_status_idx = i;
                  end
                  for(int i=0; i < old_flash_status_idx; i++) begin
                    `uvm_info(`gfn, {"Clearing item ",
                                     $sformatf("(0x%0x) from queue: 'tl_ul_old_flash_status_q'",
                                               tl_ul_old_flash_status_q[0])}, UVM_DEBUG)
                    void'(tl_ul_old_flash_status_q.pop_front());
                  end

                  // GMV value will be push to the queue later, before we update the RAL
                  // so we only push the current spi_side_flash_status (prior to updating)
                  // onto the tl_ul_old_flash_status_q if the value is not the same
                  if (`gmv(ral.flash_status) != spi_side_flash_status) begin
                    `uvm_info(`gfn, {"Pushing spi_side_flash_status=",
                                     $sformatf("0x%0x onto 'tl_ul_old_flash_status_q'",
                                               spi_side_flash_status)}, UVM_DEBUG)

                    tl_ul_old_flash_status_q.push_back(spi_side_flash_status);
                  end
                  print_str  = {"Clear 'tl_ul_old_flash_status_q' + populate with old_flash_status",
                                $sformatf(" (from before flash_status was committed) = 0x%0x",
                                          old_flash_status),
                                $sformatf(" spi_side_flash_status(old_flash_status)=0x%0x",
                                          spi_side_flash_status)};

                  `uvm_info(`gfn, print_str , UVM_DEBUG)

                  `uvm_info(`gfn, {$sformatf("Update spi_side_flash_status=0x%0x",
                                             tl_ul_fuzzy_flash_status_q[idx]),
                                   " with the predicted value which was committed"}, UVM_DEBUG)
                  spi_side_flash_status = tl_ul_fuzzy_flash_status_q[idx];
                  for(int i=0; i <=idx; i++) begin
                    `uvm_info(`gfn, $sformatf("Popping tl_ul_fuzzy_flash_status_q[i=%0d] = 0x%0x",
                                              i,tl_ul_fuzzy_flash_status_q[0]), UVM_DEBUG)
                    void'(tl_ul_fuzzy_flash_status_q.pop_front());
                  end
                end // if ( different_ral_value && idx >=0 &&...
              end // if (tl_ul_fuzzy_flash_status_q.size > 0)

              tl_ul_old_flash_status_q.push_back(`gmv(ral.flash_status));
              `uvm_info(`gfn, $sformatf("Pushing 0x%0x, on 'tl_ul_old_flash_status_q'",
                                        `gmv(ral.flash_status)),
                        UVM_DEBUG)

              // tl_ul_old_flash_status_q will have up to 2 items max. That's because once CSB goes
              // high, if SW reads flash_Status we may get the "older old" flash_status or the newer
              //  "old" value depending on when the read arrives
              while(tl_ul_old_flash_status_q.size > 2) begin
                `uvm_info(`gfn, {"Clearing item ",
                                 $sformatf("(0x%0x) from queue: 'tl_ul_old_flash_status_q'",
                                           tl_ul_old_flash_status_q[0])}, UVM_DEBUG)
                void'(tl_ul_old_flash_status_q.pop_front());
              end


              // Update flash_status predicted value
              `DV_CHECK_EQ_FATAL( ral.flash_status.predict(.value(spi_side_flash_status),
                                                           .kind(UVM_PREDICT_READ)), 1,
                                  "ral.flash_status.predict did not succeed")
              `uvm_info(`gfn, {"Updated TL-UL flash_status (2nd time) due to short command (2B)"
                               , $sformatf(" CSR to: %p",spi_side_flash_status)}, UVM_DEBUG)


            end // if (csb_active)
            `uvm_info(`gfn, "Terminating thread due to CSB not active", UVM_DEBUG)
          end
          begin
            // Terminating thread here if CSB becomes active again
            @(negedge cfg.spi_host_agent_cfg.vif.csb[FW_FLASH_CSB_ID]);
            `uvm_info(`gfn, "Terminating thread due to CSB becoming active again", UVM_DEBUG)
          end
        join_any
        disable fork;

        if (!csb_active || // Either CSB was inactive at the time
            cfg.spi_host_agent_cfg.vif.csb[FW_FLASH_CSB_ID]===0 // Or CSB is active now
            ) begin
          // store the item in a queue as. TL-UL side updates on SPI-side on each 8th SCK cycle
          tl_ul_side_flash_status_q.push_back(flash_status);
          `uvm_info(`gfn, $sformatf(
                            "SW Write to flash_status (0x%0x) (tl_ul_side_flash_status_q.size=%0d)",
                                    flash_status, tl_ul_side_flash_status_q.size), UVM_DEBUG)
        end

      end
    end join_none

  endtask // populate_tl_ul_side_flash_status_q


  // send out SPI data from tx_fifo and fetch more data from sram to fifo
  virtual function void sendout_spi_tx_data(bit [31:0] data_act);

    if (tx_word_q.size > 0) begin
      bit [31:0] data_exp     = tx_word_q.pop_front();
      if (cfg.spi_host_agent_cfg.bits_to_transfer == 7) begin
        if (cfg.spi_host_agent_cfg.device_bit_dir == 1)  begin
          data_exp[7] = 0;
        end else begin
          data_exp[0] = 0;
        end
      end
      `DV_CHECK_EQ(data_act, data_exp, "Compare SPI TX data")
    end else begin // underflow
      // TODO coverage sample
      `uvm_info(`gfn, $sformatf("TX underflow data: 0x%0h", data_act), UVM_MEDIUM)
    end
  endfunction

  // Check if opcode is enabled and returns index of enabled opcode
  // Checks if there are duplicate enabled opcodes - not proper config
  // HW parses commands this way
  virtual function check_opcode_enable(bit [7:0] q_opcode, ref bit enable, ref bit [4:0] en_idx);
    enable = 0;
    en_idx = 24; // Larger than num of cmd_info if not enabled
    for (int i = 0; i<24; i++)  begin
      if (q_opcode == `gmv(ral.cmd_info[i].opcode) && `gmv(ral.cmd_info[i].valid) == 1) begin
        `DV_CHECK_EQ(enable, 0, "Each CMD_INFO slot should have unique opcode")
        enable = 1;
        en_idx = i;
      end
    end
  endfunction

  // Task that compares passthrough opcode and first 3B of address
  // TODO modify to check opcode, address and payload
  virtual function void compare_pass_opcode_addr(bit [31:0] data_act);
    bit enabled;
    bit [4:0] en_idx;
    bit [7:0] opcode = data_act[7:0];
    bit [4:0] cmd_index = opcode / 32;
    bit [4:0] cmd_offset = opcode % 32;
    bit [31:0] mask_swap = `gmv(ral.addr_swap_mask.mask);
    bit [31:0] data_swap = `gmv(ral.addr_swap_data.data);
    check_opcode_enable(opcode, enabled, en_idx);
    if (enabled && (`gmv(ral.cmd_filter[cmd_index].filter[cmd_offset]) == 0)) begin
      bit [31:0] data_exp     = rx_word_q.pop_front();
      if (`gmv(ral.cmd_info[en_idx].addr_swap_en) == 1) begin // Addr Swap enable
        for (int i = 0; i < 24; i++) begin // TODO add 4B Address Support
          if (mask_swap[i] == 1) begin
            data_exp[i+8] = data_swap[i];
          end
        end
      end
      `DV_CHECK_EQ(data_act, data_exp, "Compare PASSTHROUGH Data")
    end
  endfunction

  // reinitialises the scoreboard's memory models
  function void clear_mems();
    spi_mem.init();
    tx_mem.init();
    rx_mem.init();
  endfunction : clear_mems

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    intr_trigger_pending = ral.intr_state.get_reset();
    tx_word_q.delete();
    rx_word_q.delete();
    spi_passthrough_downstream_q.delete();
    tpm_read_sw_q.delete();
    tpm_hw_reg_pre_val_aa.delete();

    // used in seq
    cfg.next_read_buffer_addr = 0;
    cfg.read_buffer_ptr  = 0;

    read_buffer_watermark_triggered = 0;

    spi_side_flash_status = `gmv(ral.flash_status);

    clear_mems();
  endfunction

  function void check_phase(uvm_phase phase);
    bit [TL_DW-1:0]  interrupt_mask = 'hFFFF_FFFF;
    super.check_phase(phase);
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(spi_item, upstream_spi_host_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(spi_item, upstream_spi_device_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(spi_item, upstream_spi_req_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(spi_item, downstream_spi_host_fifo)
    `DV_CHECK_EQ(tx_word_q.size, 0)
    `DV_CHECK_EQ(rx_word_q.size, 0)
    `DV_CHECK_EQ(spi_passthrough_downstream_q.size, 0)
    `DV_CHECK_EQ(upload_cmd_q.size, 0)
    `DV_CHECK_EQ(upload_addr_q.size, 0)
    `DV_CHECK_EQ(tpm_read_sw_q.size, 0)
    //Checking only event type interrupts
    interrupt_mask[5] = 0; //TPM header non emtpy is a status interrupt
    `DV_CHECK_EQ(|(intr_trigger_pending & interrupt_mask) , 0)
  endfunction
endclass
