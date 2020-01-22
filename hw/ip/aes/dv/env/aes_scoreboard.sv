// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
import aes_model_dpi_pkg::*;
import aes_pkg::*;

class aes_scoreboard extends cip_base_scoreboard #(
    .CFG_T(aes_env_cfg),
    .RAL_T(aes_reg_block),
    .COV_T(aes_env_cov)
  );
  `uvm_component_utils(aes_scoreboard)

  `uvm_component_new

  // local variables
  aes_seq_item dut_item;
  // TLM agent fifos

  // local queues to hold incoming packets pending comparison
  mailbox #(aes_seq_item) dut_fifo;                                   // all incoming TL transactions will be written to this one
  mailbox #(aes_seq_item) ref_fifo;                                   // this will be a clone of the above before the result has been calculated by the dut!


  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    dut_fifo = new();
    ref_fifo = new();
    dut_item = new("dut_item");
  endfunction


  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction


  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      compare();
    join_none
  endtask


  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel = DataChannel);
    uvm_reg        csr;
    aes_seq_item   ref_item;
    bit            do_read_check = 1'b0;
    bit            write         = item.is_write();
    uvm_reg_addr_t csr_addr      = get_normalized_addr(item.a_addr);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.csr_addrs}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    if (channel == AddrChannel) begin
      // if incoming access is a write to a valid csr, then make updates right away
      if (write) begin
        void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
      end
      case (csr.get_name())
        // add individual case item for each csr
        "ctrl": begin
          {dut_item.allow_data_ovrwrt, dut_item.man_trigger,dut_item.key_size,dut_item.mode}
          = item.a_data[5:0];
        end
        "key0": begin
          dut_item.key[0] = item.a_data;
        end
        "key1": begin
          dut_item.key[1] = item.a_data;
        end
        "key2": begin
          dut_item.key[2] = item.a_data;
        end
        "key3": begin
          dut_item.key[3] = item.a_data;
        end
        "key4": begin
          dut_item.key[4] = item.a_data;
        end
        "key5": begin
          dut_item.key[5] = item.a_data;
        end
        "key6": begin
          dut_item.key[6] = item.a_data;
        end
        "key7": begin
          dut_item.key[7] = item.a_data;
        end

        "data_in0" :begin
          dut_item.data_in[0]     = item.a_data;
          dut_item.data_in_vld[0] = 1;
        end

        "data_in1" :begin
          dut_item.data_in[1]     = item.a_data;
          dut_item.data_in_vld[1] = 1;
        end

        "data_in2" :begin
          dut_item.data_in[2]     = item.a_data;
          dut_item.data_in_vld[2] = 1;
        end

        "data_in3": begin
          dut_item.data_in[3]     = item.a_data;
          dut_item.data_in_vld[3] = 1;
        end

        "trigger": begin
          if (item.a_data[0]) begin
            `downcast(ref_item, dut_item.clone());
            ref_fifo.put(ref_item);
          end
        end

        "status": begin
            //TBD
        end

        default: begin
         // DO nothing- trying to write to a read only register
        end
      endcase

      // forward Item and clear valid bits
        if (!dut_item.man_trigger && (& dut_item.data_in_vld)) begin
        `downcast(ref_item, dut_item.clone());
        ref_fifo.put(ref_item);
        ref_item = new();
        dut_item.data_in_vld = '0;
      end
    end


    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    `uvm_info(`gfn, $sformatf("\n\t ---| channel  %h", channel), UVM_HIGH)
    if (!write && channel == DataChannel) begin
      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                     $sformatf("reg name: %0s", csr.get_full_name()))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
        `uvm_info(`gfn, $sformatf("\n\t ----| SAW READ - %s data %02h",csr.get_name(),  item.d_data)
                  , UVM_HIGH)

      case (csr.get_name())
        "data_out0": begin
          dut_item.data_out[0]     = item.d_data;
          dut_item.data_out_vld[0] = 1;
        end
        "data_out1": begin
          dut_item.data_out[1]     = item.d_data;
          dut_item.data_out_vld[1] = 1;
        end
        "data_out2": begin
          dut_item.data_out[2]     = item.d_data;
          dut_item.data_out_vld[2] = 1;
        end
        "data_out3": begin
          dut_item.data_out[3]     = item.d_data;
          dut_item.data_out_vld[3] = 1;
        end
      endcase
        if (&dut_item.data_out_vld) begin
        dut_fifo.put(dut_item);
        dut_item = new();
      end
    end
  endtask


  virtual task compare();
    string txt="";
    forever begin
      aes_seq_item rtl_item;
      aes_seq_item c_item;
      bit [127:0] calc_data;

      `uvm_info(`gfn, $sformatf("\n\t ----| TRYING to get item "), UVM_HIGH)
      dut_fifo.get(rtl_item);
      ref_fifo.get(c_item );
      `uvm_info(`gfn, $sformatf("\n\t ----| GOT item "), UVM_HIGH)

      aes_crypt(1'b0, c_item.mode, c_item.key_size, c_item.key, c_item.data_in, c_item.data_out);
         `uvm_info(`gfn, $sformatf("\n\t ----| printing C MODEL %s", c_item.convert2string() )
                   , UVM_HIGH)

      if (!rtl_item.compare(c_item)) begin
        txt = {txt,  $sformatf("\n\t ----| RTL_ITEM %s \n\t ", rtl_item.convert2string())};
        txt = {txt, $sformatf("\n\t ----| printing C MODEL %s", c_item.convert2string() )};
        txt = {txt,  $sformatf("\n\t ----| \t\t\t  DATA OUTPUT \t\t  |---- ")};
        txt = {txt, $sformatf("\n\t ----| \t\t\t  RTL \t\t REF \t  |---- ")};
        foreach (rtl_item.data_out[i]) begin
          txt = {txt, $sformatf("\n\t ----| [%d] \t %02h \t %02h |----", i, rtl_item.data_out[i],
                                c_item.data_out[i])};
        end
        `uvm_fatal(`gfn, $sformatf("\t TEST FAILED ITEMS DOES NOT MATCH \n\t %s \n",txt))
      end else begin
        `uvm_info(`gfn, $sformatf("\n\t ----|    ITEMS MATCHED    |-----"), UVM_LOW)
      end
    end
  endtask


  virtual function void phase_ready_to_end(uvm_phase phase);
    if (phase.get_name() != "run") return;
    if ( (dut_fifo.num() != 0 ) || (ref_fifo.num() != 0) ) begin
      phase.raise_objection(this, "fifos still has data");
      fork begin
        wait_fifo_empty();
        phase.drop_objection(this);
      end
      join_none
    end
  endfunction


  virtual task wait_fifo_empty();
    wait ((dut_fifo.num() == 0 ) && (ref_fifo.num() == 0));
  endtask


  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
  endfunction


  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    `DV_EOT_PRINT_MAILBOX_CONTENTS(aes_seq_item, dut_fifo)
    `DV_EOT_PRINT_MAILBOX_CONTENTS(aes_seq_item, ref_fifo)
  endfunction


  function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    `uvm_info(`gfn, $sformatf("%s", cfg.convert2string()), UVM_LOW)
  endfunction

endclass
