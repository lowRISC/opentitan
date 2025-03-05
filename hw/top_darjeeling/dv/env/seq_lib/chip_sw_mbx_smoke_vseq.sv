// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// (SW counterpart -> mbx_smoketest.c)
//
// - Basic mailbox read/write sequence
//   - (vseq) System Host/SoC sends request, (sw) OT/Ibex generates a response
//   - Randomly select between all mailboxes
//   - Requester (SystemHost/SoC) switches between IRQ-based/polling-based
//     UVM testbench routines

class chip_sw_mbx_smoke_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_mbx_smoke_vseq)
  `uvm_object_new

  // This is limited by the provisioned mbx memory size.
  localparam uint MaxNumDWORDS = 8;

  rand int rNumTxns;
  constraint num_txns_c {
    // This limits the length of the test.
    rNumTxns inside {[chip_common_pkg::NUM_MBXS-1:15]};
  }

  // mbxIdx is random-cyclic through the mailboxes in the system
  randc uint rMbxIdx;
  constraint mbx_idx_c {
    rMbxIdx inside {[0:chip_common_pkg::NUM_MBXS-1]};
  }

  typedef uvm_reg_data_t DWORDS_array [MaxNumDWORDS];
  rand DWORDS_array rData;

  typedef enum bit {
    rd,
    wr
  } rw_t;
  typedef enum bit {
    poll,
    irq
  } wait_t;
  typedef enum bit {
    tlul,
    jtag
  } ral_access_t;
  typedef struct {
    mbx_soc_reg_block ral;
    ral_access_t ral_access_method;
    string ralname;
  } ralmap_elem_t;
  ralmap_elem_t ralmap[uint];
  ral_access_t ral_access_method;

  bit [7:0] kSoftwareBarrier[] = '{0};
  bit [7:0] kNumTxns[] = '{0};


  virtual task pre_start();
    super.pre_start();
    // Initialize the ralmap structure
    ralmap[0] = '{cfg.chip_soc_mbx_ral.mbx0_soc,      tlul, "mbx0"};
    ralmap[1] = '{cfg.chip_soc_mbx_ral.mbx1_soc,      tlul, "mbx1"};
    ralmap[2] = '{cfg.chip_soc_mbx_ral.mbx2_soc,      tlul, "mbx2"};
    ralmap[3] = '{cfg.chip_soc_mbx_ral.mbx3_soc,      tlul, "mbx3"};
    ralmap[4] = '{cfg.chip_soc_mbx_ral.mbx4_soc,      tlul, "mbx4"};
    ralmap[5] = '{cfg.chip_soc_mbx_ral.mbx5_soc,      tlul, "mbx5"};
    ralmap[6] = '{cfg.chip_soc_mbx_ral.mbx6_soc,      tlul, "mbx6"};
    ralmap[7] = '{cfg.chip_soc_dbg_ral.mbx_jtag_soc,  jtag, "mbx_jtag"};
    ralmap[8] = '{cfg.chip_soc_mbx_ral.mbx_pcie0_soc, tlul, "mbx_pcie0"};
    ralmap[9] = '{cfg.chip_soc_mbx_ral.mbx_pcie1_soc, tlul, "mbx_pcie1"};
  endtask

  // Wrap accesses to both the mbx_ral and the dbg_ral
  // - This keeps the main routine clean
  // - TODO: Remove/Refactor this away when the dbg_ral can make
  //         frontdoor accesses successfully.
  virtual task access_wrapper(input  uvm_object ptr, // reg or mem, not field
                              input  rw_t read_or_write,
                              output uvm_reg_data_t rdata,
                              input  uvm_reg_data_t wdata = '0);
    uvm_reg_addr_t addr;
    uvm_mem mem;
    uvm_reg register;
    bit addr_is_reg;
    if ($cast(register, ptr)) begin
      addr_is_reg = 1'b1;
      addr = register.get_address();
    end else if ($cast(mem, ptr)) begin
      addr_is_reg = 1'b0;
      addr = mem.get_address();
    end else begin
      `uvm_fatal(`gfn, "uvm_object passed to access_wrapper not reg or mem!")
    end

    case (ral_access_method)
      tlul: begin
        if (addr_is_reg) begin
          if (read_or_write == rd) csr_rd(register, rdata);
          else                     csr_wr(register, wdata);
        end else begin
          if (read_or_write == rd) mem_rd(mem, 0, rdata);
          else                     mem_wr(mem, 0, wdata);
        end
      end
      jtag: begin
        if (read_or_write == rd) jtag_riscv_agent_pkg::jtag_read_csr(
          addr, p_sequencer.jtag_sequencer_h, rdata);
        else jtag_riscv_agent_pkg::jtag_write_csr(
          addr, p_sequencer.jtag_sequencer_h, wdata);
      end
      default: `uvm_fatal(`gfn, "ral_access_method requested not tlul or jtag!")
    endcase
  endtask

  virtual task requester_mbx_txn(uint mbxIdx,
                                 uint numDWORDS,
                                 uvm_reg_data_t DWORDS [],
                                 wait_t poll_or_irq);

    mbx_soc_reg_block mbx_ral = ralmap[mbxIdx].ral;
    string ralname = ralmap[mbxIdx].ralname;

    uvm_reg_data_t rdata, wdata;

    uvm_reg_data_t DWORD_req_q[$];
    uvm_reg_data_t DWORD_rsp_q[$];
    `DV_CHECK(DWORDS.size() >= numDWORDS,
              $sformatf({"Too few DWORDS passed to fun, ",
                        "numDWORDS = %0d, DWORDS.size() = %0d"},
                        numDWORDS, DWORDS.size()));

    // Start the transaction : requester writes data into the imbx
    begin : requester_imbx_write

      // Push DWORDS to the write-data register

      `uvm_info(`gfn,
                $sformatf("Requester: Writing %0d DWORDS to soc.wdata",
                          numDWORDS),
                UVM_LOW)
      for(int unsigned i = 0; i < numDWORDS; i++) begin
        wdata = DWORDS[i];
        DWORD_req_q.push_back(wdata);
        access_wrapper(mbx_ral.wdata, wr, rdata, wdata);
        `uvm_info(`gfn, $sformatf("Wrote 0x%0x to soc.wdata", wdata), UVM_MEDIUM)
      end

      // Write to soc_control to indicate the imbx write is complete
      // - Set the .go bit to start the txn.
      // - Set the .doe_intr_en bit if we are handling as an irq externally

      wdata = '0;
      if (poll_or_irq == irq) wdata[mbx_ral.soc_control.doe_intr_en.get_lsb_pos()] = 1'b1;
      wdata[mbx_ral.soc_control.go.get_lsb_pos()] = 1'b1;
      access_wrapper(mbx_ral.soc_control, wr, rdata, wdata);
    end // requester_imbx_write

    `uvm_info(`gfn, $sformatf("SoC completed write to %s.", ralname), UVM_LOW)
    `uvm_info(`gfn,
              "SoC set .go=1, waiting for return message from core.",
              UVM_MEDIUM)

    begin : requester_ombx_read

      // First, wait until the mailbox reports the outbox message is ready

      case (poll_or_irq)
        poll: begin
          `uvm_info(`gfn, "SoC polling for mbx.soc_status.ready = 1'b1", UVM_LOW)
          `DV_SPINWAIT(
            do begin
              access_wrapper(mbx_ral.soc_status, rd, rdata, wdata);
            end while (dv_base_reg_pkg::get_field_val(mbx_ral.soc_status.ready, rdata) != 1'b1);,
            "Timeout while polling for mbx.soc_status.ready = '1.")
        end
        irq: begin
          `uvm_info(`gfn, "SoC waiting for external interrupt.", UVM_LOW)
          `DV_SPINWAIT(wait( // [3] == doe_intr_o
            cfg.chip_vif.darjeeling_mbx_if.interrupts[mbxIdx][3] == 1'b1);)
          `uvm_info(`gfn, "SoC received external interrupt.", UVM_MEDIUM)

          // > Upon receiving an interrupt, it checks the DOE Status Register
          // > .ready bit to see if the object is ready.
          access_wrapper(mbx_ral.soc_status, rd, rdata, wdata);
          if (dv_base_reg_pkg::get_field_val(mbx_ral.soc_status.ready, rdata) != 1'b1) begin
            `uvm_fatal(`gfn, "soc_status.ready not set after interrupt!")
          end
        end
        default: ;
      endcase // poll_or_irq

      `uvm_info(`gfn,
                {"SoC read that soc_status.ready = 1'b1.",
                " Outbox message is now ready."},
                UVM_LOW)

      `uvm_info(`gfn, "Read the following data from the outbox:", UVM_MEDIUM)
      for(int unsigned i = 0; i < numDWORDS; i++) begin
        access_wrapper(mbx_ral.rdata, rd, rdata, wdata);
        DWORD_rsp_q.push_back(rdata);
        `uvm_info(`gfn, $sformatf("Read 0x%0x from soc.rdata", rdata), UVM_MEDIUM)
        // Write anything to RDATA to advance to the next word.
        access_wrapper(mbx_ral.rdata, wr, rdata, $urandom);
      end

      // Write 1'b1 to clear soc_status.doe_intr_status, acknowledging the
      // interrupt.
      // - Even if soc_control.doe_intr_en = 1'b0, the irq asserts regardless.
      // - All other fields are RO, so we don't need to bother reading first.
      wdata = '0;
      wdata[mbx_ral.soc_status.doe_intr_status.get_lsb_pos()] = 1'b1;
      access_wrapper(mbx_ral.soc_status, wr, rdata, wdata);
    end // requester_ombx_read

    // Check the data returned by the responder matches our expectation.
    for(int unsigned i = 0; i < numDWORDS; i++) begin
      uvm_reg_data_t DWORD_req, DWORD_rsp, DWORD_rsp_expected;
      DWORD_req = DWORD_req_q.pop_front();
      DWORD_rsp = DWORD_rsp_q.pop_front();
      // Apply matching transformation
      DWORD_rsp_expected = DWORD_req + 1;
      // Check received response against expected response
      `DV_CHECK_EQ(DWORD_rsp[TL_DW-1:0], DWORD_rsp_expected[TL_DW-1:0])
    end
  endtask : requester_mbx_txn

  virtual task body();
    super.body();

    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "init_complete")

    kNumTxns[0] = rNumTxns;
    sw_symbol_backdoor_overwrite("kNumTxns", kNumTxns);

    // Add synchronization point for the sw to read 'kNumTxns'
    kSoftwareBarrier[0] = 1;
    `uvm_info(`gfn, $sformatf("Settings kSoftwareBarrier = %0d", 1), UVM_LOW)
    sw_symbol_backdoor_overwrite("kSoftwareBarrier", kSoftwareBarrier);

    // The sw will now read the number of transactions, then go into WFI
    // awaiting the first request message
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "received_tb_cfg")

    begin: test_stimulus
      for(int unsigned i = 1; i <= rNumTxns; i++) begin
        wait_t poll_or_irq;
        uint numDWORDS = $urandom_range(1, MaxNumDWORDS);
        // Use randomized data each time.
        `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rData)
        // Choose a randomized mailbox instance for each txn
        `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rMbxIdx)
        `DV_CHECK_STD_RANDOMIZE_FATAL(poll_or_irq)
        `uvm_info(`gfn,
                  $sformatf({"Requester: Starting txn %0d/%0d",
                             " with %0d DWORDS in mbx[%0d]"},
                            i, rNumTxns, numDWORDS, rMbxIdx),
                  UVM_LOW)
        // Set the following class variable, which is read by access_wrapper()
        ral_access_method = ralmap[rMbxIdx].ral_access_method;
        requester_mbx_txn(
          .mbxIdx(rMbxIdx),
          .numDWORDS(numDWORDS),
          .DWORDS(rData),
          .poll_or_irq(poll_or_irq));
        `uvm_info(`gfn,
                  $sformatf({"Return message from core received & checked.",
                            " Txn %0d/%0d complete"}, i, rNumTxns),
                  UVM_LOW)
        #10us; // Small delay gives time for the sw to poll the 'busy' status
               // bit, and then unmask the 'ready' irq.
      end
    end // test_stimulus

    `uvm_info(`gfn, "Vseq stimulus completed sucessfully.", UVM_LOW)
  endtask

endclass
