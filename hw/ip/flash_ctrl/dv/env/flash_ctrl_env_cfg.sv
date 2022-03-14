// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_env_cfg extends cip_base_env_cfg #(
  .RAL_T(flash_ctrl_core_reg_block)
);

  // Memory backdoor util instances for each partition in each bank.
  mem_bkdr_util mem_bkdr_util_h[flash_dv_part_e][flash_ctrl_pkg::NumBanks];

  // seq cfg
  flash_ctrl_seq_cfg seq_cfg;

  // interface
  virtual flash_ctrl_if flash_ctrl_vif;
  virtual clk_rst_if clk_rst_vif_flash_ctrl_eflash_reg_block;

  // knobs
  // ral.status[init_wip] status is set for the very first clock cycle right out of reset.
  // This causes problems in the read value especially in CSR tests.
  int post_reset_delay_clks = 1;

  // Knob for blocking host reads
  bit block_host_rd = 1;

  // Knob for scoreboard write and check on reads
  bit scb_check = 0;

  // Knob for scoreboard set expected alert
  bit scb_set_exp_alert = 0;

  // Max delay for alerts in clocks
  uint alert_max_delay;

  // read data by host if
  data_q_t flash_rd_data;

  `uvm_object_utils_begin(flash_ctrl_env_cfg)

  `uvm_object_utils_end

  `uvm_object_new

  string flash_ral_name = "flash_ctrl_eflash_reg_block";

  virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
    list_of_alerts = flash_ctrl_env_pkg::LIST_OF_ALERTS;
    has_shadowed_regs = 1;
    tl_intg_alert_name = "fatal_intg_err";

    // Set up second RAL model for Flash memory
    ral_model_names.push_back(flash_ral_name);

    // both RAL models use same clock frequency
    clk_freqs_mhz[flash_ral_name] = clk_freq_mhz;

    super.initialize(csr_base_addr);

    shadow_update_err_status_fields[ral.err_code.update_err] = 1;
    shadow_storage_err_status_fields[ral.fault_status.storage_err] = 1;

    // create the seq_cfg and call configure
    seq_cfg = flash_ctrl_seq_cfg::type_id::create("seq_cfg");
    seq_cfg.configure();

    // set num_interrupts & num_alerts
    begin
      uvm_reg rg = ral.get_reg_by_name("intr_state");
      if (rg != null) begin
        num_interrupts = ral.intr_state.get_n_used_bits();
      end
    end

    alert_max_delay = 20000;
    `uvm_info(`gfn, $sformatf("ral_model_names: %0p", ral_model_names), UVM_LOW)
  endfunction : initialize

  // Backdoor initialize flash memory elements.
  //
  // Applies the initialization scheme to the given flash partition in all banks.
  // part is the type of flash partition.
  // scheme is the type of initialization to be done.
  virtual function void flash_mem_bkdr_init(flash_dv_part_e part = FlashPartData,
                                            flash_mem_init_e scheme);
    case (scheme)
      FlashMemInitSet: begin
        foreach (mem_bkdr_util_h[part][i]) mem_bkdr_util_h[part][i].set_mem();
      end
      FlashMemInitClear: begin
        foreach (mem_bkdr_util_h[part][i]) mem_bkdr_util_h[part][i].clear_mem();
      end
      FlashMemInitRandomize: begin
        foreach (mem_bkdr_util_h[part][i]) mem_bkdr_util_h[part][i].randomize_mem();
      end
      FlashMemInitInvalidate: begin
        foreach (mem_bkdr_util_h[part][i]) mem_bkdr_util_h[part][i].invalidate_mem();
      end
    endcase
  endfunction : flash_mem_bkdr_init

  // Reads flash mem contents via backdoor.
  //
  // The addr arg need not be word aligned - its the same addr programmed into the `control` CSR.
  // TODO: add support for partition.
  virtual function void flash_mem_bkdr_read(flash_op_t flash_op, ref data_q_t data);
    flash_mem_addr_attrs             addr_attrs = new(flash_op.addr);
    bit                  [TL_AW-1:0] read_addr;

    if (flash_op.op == flash_ctrl_pkg::FlashOpErase) begin
      case (flash_op.erase_type)
        flash_ctrl_pkg::FlashErasePage: begin
          read_addr = addr_attrs.page_start_addr;
          flash_op.num_words = FlashNumBusWordsPerPage;
        end
        flash_ctrl_pkg::FlashEraseBank: begin
          read_addr = 0;
          case (flash_op.partition)
            FlashPartData: begin
              flash_op.num_words = FlashNumBusWordsPerBank;
            end
            FlashPartInfo: begin
              flash_op.num_words = InfoTypeBusWords[0];
            end
            default: begin
              `uvm_fatal(`gfn, $sformatf(
                         {
                           "Invalid partition for bank_erase: %0s. ",
                           "Bank erase is only valid in the data partition ",
                           "(FlashPartData) and the first info partition ",
                           "(FlashPartInfo)."
                         },
                         flash_op.partition.name()
                         ))
            end
          endcase
        end
        default: begin
          `uvm_fatal(`gfn, $sformatf("Invalid erase_type: %0s", flash_op.erase_type.name()))
        end
      endcase
    end else begin  // FlashOpProgram, FlashOpRead
      read_addr = addr_attrs.bank_addr;
    end

    data.delete();
    for (int i = 0; i < flash_op.num_words; i++) begin
      data[i] = mem_bkdr_util_h[flash_op.partition][addr_attrs.bank].read32(read_addr);
      `uvm_info(`gfn, $sformatf(
                "flash_mem_bkdr_read: partition = %s , {%s} = 0x%0h",
                flash_op.partition.name(),
                addr_attrs.sprint(),
                data[i]
                ), UVM_MEDIUM)
      read_addr += TL_DBW;
    end
  endfunction : flash_mem_bkdr_read

  // Writes the flash mem contents via backdoor.
  //
  // The addr need not be bus word aligned, Its the same addr programmed into the `control` CSR.
  // The data queue is sized for the bus word.
  // TODO: support for partition.
  virtual function void flash_mem_bkdr_write(flash_op_t flash_op, flash_mem_init_e scheme,
                                             data_q_t data = {});
    flash_mem_addr_attrs addr_attrs = new(flash_op.addr);
    logic [TL_DW-1:0] wr_data;

    // Randomize the lower half-word (if Xs) if the first half-word written in the below loop is
    // corresponding upper half-word.
    if (addr_attrs.bank_addr[flash_ctrl_pkg::DataByteWidth-1]) begin
      _randomize_uninitialized_half_word(.partition(flash_op.partition), .bank(addr_attrs.bank),
                                         .addr(addr_attrs.word_addr));
    end

    case (scheme)
      FlashMemInitCustom: begin
        flash_op.num_words = data.size();
      end
      FlashMemInitSet: begin
        wr_data = {flash_ctrl_pkg::DataWidth{1'b1}};
      end
      FlashMemInitClear: begin
        wr_data = {flash_ctrl_pkg::DataWidth{1'b0}};
      end
      FlashMemInitInvalidate: begin
        wr_data = {flash_ctrl_pkg::DataWidth{1'bx}};
      end
    endcase

    for (int i = 0; i < flash_op.num_words; i++) begin
      logic [TL_DW-1:0] loc_data = (scheme == FlashMemInitCustom) ? data[i] :
          (scheme == FlashMemInitRandomize) ? $urandom() : wr_data;

      _flash_full_write(flash_op.partition, addr_attrs.bank, addr_attrs.bank_addr, loc_data);

      `uvm_info(`gfn, $sformatf(
                "flash_mem_bkdr_write: partition = %s , {%s} = 0x%0h",
                flash_op.partition.name(),
                addr_attrs.sprint(),
                loc_data
                ), UVM_MEDIUM)
      addr_attrs.incr(TL_DBW);
    end

    // Randomize the upper half-word (if Xs) if the last word written in the above loop is
    // corresponding lower half-word.
    if (addr_attrs.bank_addr[flash_ctrl_pkg::DataByteWidth-1]) begin
      _randomize_uninitialized_half_word(.partition(flash_op.partition), .bank(addr_attrs.bank),
                                         .addr(addr_attrs.bank_addr));
    end
  endfunction : flash_mem_bkdr_write

  // Helper function that takes a 32-bit data and correctly populates the integrity ECC
  //
  function void _flash_full_write(flash_dv_part_e partition, uint bank,
                                  // bus word aligned address
                                  bit [TL_AW-1:0] addr,
                                  bit [TL_DW-1:0] wr_data);

    // read back the full flash word
    logic [flash_ctrl_pkg::DataWidth-1:0] data;
    logic [7:0] intg_data;
    logic is_upper = addr[flash_ctrl_pkg::DataByteWidth-1];
    logic [TL_AW-1:0] aligned_addr = addr;

    if (is_upper) begin
      aligned_addr = {addr[TL_AW-1:FlashDataByteWidth], {FlashDataByteWidth{1'b0}}};
    end

    // get the full flash word
    data = mem_bkdr_util_h[partition][bank].read64(aligned_addr);

    // writing the upper portion of the flash word
    if (is_upper) begin
      data = {wr_data, data[TL_DW-1:0]};
    end else begin
      data = {data[flash_ctrl_pkg::DataWidth-:TL_DW], wr_data};
    end

    // calculate truncated integrity
    {intg_data, data} = prim_secded_pkg::prim_secded_hamming_72_64_enc(data);

    // program fully via backdoor
    mem_bkdr_util_h[partition][bank].write64(aligned_addr, {intg_data[3:0], data});

  endfunction


  // Helper function that randomizes the half-word at the given address if unknown.
  //
  // When the 'other' flash half-word is being written by the flash_mem_bkdr_write() method, the
  // half-word at the given address needs to also be updated, of the data at that address is
  // unknown. This is needed because the flash_ctrl RTL internally fetches full words. This method
  // randomizes the data at the given address via backdoor.
  function void _randomize_uninitialized_half_word(flash_dv_part_e partition, uint bank,
                                                   bit [TL_AW-1:0] addr);
    logic [TL_DW-1:0] data = mem_bkdr_util_h[partition][bank].read32(addr);
    if ($isunknown(data)) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(data)
      `uvm_info(`gfn, $sformatf("Data at 0x%0h is Xs, writing random 0x%0h", addr, data), UVM_HIGH)
      _flash_full_write(partition, bank, addr, data);
    end
  endfunction

  // Checks flash mem contents via backdoor.
  //
  // The addr need not be bus word aligned. Its the same addr programmed into the `control` CSR.
  // The exp data queue is sized for the bus word.
  // TODO: support for partition.
  virtual function void flash_mem_bkdr_read_check(flash_op_t flash_op, const ref data_q_t exp_data);
    data_q_t data;
    flash_mem_bkdr_read(flash_op, data);
    foreach (data[i]) begin
      `DV_CHECK_CASE_EQ(data[i], exp_data[i])
    end
  endfunction : flash_mem_bkdr_read_check

  // Verifies that the flash page / bank has indeed been erased.
  virtual function void flash_mem_bkdr_erase_check(flash_op_t flash_op, data_q_t exp_data = {});
    flash_mem_addr_attrs             addr_attrs = new(flash_op.addr);
    bit                  [TL_AW-1:0] erase_check_addr;
    string                           erase_page_num_msg;
    uint                             num_words;

    case (flash_op.erase_type)
      flash_ctrl_pkg::FlashErasePage: begin
        erase_check_addr = addr_attrs.page_start_addr;
        num_words = FlashNumBusWordsPerPage;
        erase_page_num_msg = $sformatf("page = %0d, ", addr_attrs.page);
      end
      flash_ctrl_pkg::FlashEraseBank: begin
        // This address is relative to the bank it's in.
        erase_check_addr   = 0;
        // No need to state page for bank erase.
        erase_page_num_msg = "";
        case (flash_op.partition)
          FlashPartData: begin
            num_words = FlashNumBusWordsPerBank;
          end
          FlashPartInfo: begin
            num_words = InfoTypeBusWords[0];
          end
          default: begin
            `uvm_fatal(`gfn, $sformatf(
                       {
                         "Invalid partition for bank_erase: %0s. ",
                         "Bank erase is only valid in the data partition ",
                         "(FlashPartData) and the first info partition ",
                         "(FlashPartInfo)."
                       },
                       flash_op.partition.name()
                       ))
          end
        endcase
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("Invalid erase_type: %0s", flash_op.erase_type.name()))
      end
    endcase
    `uvm_info(`gfn, $sformatf(
              {
                "flash_mem_bkdr_erase_check: Erase type = %s, bank = %0d, ",
                "partition = %s , %snum_words = %0d"
              },
              flash_op.erase_type.name(),
              addr_attrs.bank,
              flash_op.partition.name(),
              erase_page_num_msg,
              num_words
              ), UVM_MEDIUM)

    for (int i = 0; i < num_words; i++) begin
      logic [TL_DW-1:0] data;
      data = mem_bkdr_util_h[flash_op.partition][addr_attrs.bank].read32(erase_check_addr);
      `uvm_info(`gfn, $sformatf(
                {
                  "flash_mem_bkdr_erase_check: Erase type = %s, bank: %0d, ",
                  "partition: %s , %saddr: 0x%0h, data: 0x%0h"
                },
                flash_op.erase_type.name(),
                addr_attrs.bank,
                flash_op.partition.name(),
                erase_page_num_msg,
                erase_check_addr,
                data
                ), UVM_MEDIUM)
      // If the expected data is not empty then it should be taken is expected. If it is empty the
      //  default expected value is checked - which for successful erase is all 1s.
      if (exp_data.size() <= i) begin
        `DV_CHECK_CASE_EQ(data, '1)
      end else begin
        `DV_CHECK_CASE_EQ(data, exp_data[i])
      end
      erase_check_addr += TL_DBW;
    end
  endfunction : flash_mem_bkdr_erase_check

  // Function to enable changing of the expected data to be checked in the post-transaction
  // checks.
  virtual function data_q_t calculate_expected_data(flash_op_t flash_op,
                                                    const ref data_q_t exp_data);
    return exp_data;
  endfunction : calculate_expected_data

endclass
