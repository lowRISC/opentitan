// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Selectively test the JTAG DMI.
module tb_jtag_dmi;

  logic clk, rst_n;

  localparam time ClkPeriod = 10ns;
  localparam time ApplTime =  2ns;
  localparam time TestTime =  8ns;

  localparam time JTAGPeriod = 50ns;

  localparam int unsigned AW = 7;
  localparam IDCode = 32'hdeadbeef | 32'b1;

  // ----------------
  // Clock generation
  // ----------------
  initial begin
    rst_n = 0;
    repeat (3) begin
      #(ClkPeriod/2) clk = 0;
      #(ClkPeriod/2) clk = 1;
    end
    rst_n = 1;
    forever begin
      #(ClkPeriod/2) clk = 0;
      #(ClkPeriod/2) clk = 1;
    end
  end

  logic tck;

  JTAG_DV jtag_mst (tck);

  initial begin
    #100ns;
    forever begin
      tck = 1;
      #(JTAGPeriod/2);
      tck = 0;
      #(JTAGPeriod/2);
    end
  end

  // ---
  // DUT
  // ---
  DMI_BUS_DV #(
    .ADDR_WIDTH ( AW )
  ) slave_dv (clk);

  logic dut_tck, dut_tms, dut_trstn, dut_tdi, dut_tdo;
  logic start_rand;

  dm::dmi_req_t dmi_req;
  dm::dmi_resp_t dmi_resp;

  assign slave_dv.q_addr = dmi_req.addr;
  assign slave_dv.q_op = dmi_req.op;
  assign slave_dv.q_data = dmi_req.data;
  assign dmi_resp = '{
    data: slave_dv.p_data,
    resp: slave_dv.p_resp
  };

  dmi_jtag #(
    .IdcodeValue (IDCode)
  ) dut (
    .clk_i (clk),
    .rst_ni (rst_n),
    .testmode_i (1'b0),

    .dmi_rst_no (),
    .dmi_req_o (dmi_req),
    .dmi_req_valid_o (slave_dv.q_valid),
    .dmi_req_ready_i (slave_dv.q_ready),

    .dmi_resp_i (dmi_resp),
    .dmi_resp_ready_o (slave_dv.p_ready),
    .dmi_resp_valid_i (slave_dv.p_valid),

    .tck_i (dut_tck),
    .tms_i (dut_tms),
    .trst_ni (dut_trstn),
    .td_i (dut_tdi),
    .td_o (dut_tdo),
    .tdo_oe_o ()
  );

  // -------
  // Monitor
  // -------
  typedef dmi_test::dmi_monitor #(
    .AW ( AW ),
    .TA ( ApplTime ),
    .TT ( TestTime )
  ) dmi_monitor_t;

  dmi_monitor_t dmi_monitor = new (slave_dv);

  initial begin
    @(posedge start_rand);
    dmi_monitor.monitor();
  end

  // ------
  // Driver
  // ------
  typedef dmi_test::rand_dmi_slave #(
    // dmi bus interface paramaters;
    .AW ( AW ),
    // Stimuli application and test time
    .TA ( ApplTime ),
    .TT ( TestTime )
  ) dmi_rand_slave_t;

  dmi_rand_slave_t rand_dmi_slave = new (slave_dv);

  // dmi Slave.
  initial begin
    rand_dmi_slave.reset();
    @(posedge start_rand);
    rand_dmi_slave.run();
  end

  `ifdef TARGET_BSCANE

  JTAG_SIME2 #(
    .PART_NAME ("7K325T")
  ) i_jtag_sime2 (
    .TDO (jtag_mst.tdo),
    .TCK (tck),
    .TDI (jtag_mst.tdi),
    .TMS (jtag_mst.tms)
  );

  // Default part `7K325T` has an IrLength of 6.
  localparam IRLength = i_jtag_sime2.IRLength;
  localparam logic [23:0] IR_CAPTURE_VAL = 24'b010001010001010001010001,
                          BYPASS_INSTR   = 24'b111111111111111111111111,
                          IDCODE_INSTR   = 24'b001001001001001001001001,
                          USER1_INSTR    = 24'b000010100100100100100100,
                          USER2_INSTR    = 24'b000011100100100100100100,
                          USER3_INSTR    = 24'b100010100100100100100100,
                          USER4_INSTR    = 24'b100011100100100100100100;

  typedef jtag_test::riscv_dbg #(
    .IDCODE (IDCODE_INSTR[23:(24-IRLength)]),
    .DTMCSR (USER3_INSTR[23:(24-IRLength)]),
    .DMIACCESS (USER4_INSTR[23:(24-IRLength)]),
    .IrLength (IRLength),
    .TA (JTAGPeriod*0.1),
    .TT (JTAGPeriod*0.9)
  ) riscv_dbg_t;

  /// Helper function to bring instruction register values.
  // initial begin
  //   for (int i = 6; i < 25; i++) begin
  //     $display("IRLength %d: %h %h %h\n", i,
  //       (IDCODE_INSTR >> (24-i)) & (2**i-1),
  //       (USER3_INSTR >> (24-i)) & (2**i-1),
  //       (USER4_INSTR >> (24-i)) & (2**i-1));
  //   end
  // end
  `else

  assign dut_tck = tck;
  assign dut_tms = jtag_mst.tms;
  assign dut_trstn = jtag_mst.trst_n;
  assign dut_tdi = jtag_mst.tdi;
  assign jtag_mst.tdo = dut_tdo;

  typedef jtag_test::riscv_dbg #(
    .IrLength (5),
    .TA (JTAGPeriod*0.1),
    .TT (JTAGPeriod*0.9)
  ) riscv_dbg_t;
  `endif

  riscv_dbg_t::jtag_driver_t jtag_in = new (jtag_mst);
  riscv_dbg_t riscv_dbg = new (jtag_in);

  mailbox req_mbx = new, rsp_mbx = new;
  localparam NrRandomTransactions = 200;
  int unsigned nr_transactions = 0;

  initial begin
    logic [31:0] idcode;
    dm::dtmcs_t dtmcs;
    logic [4:0] opocode;
    start_rand = 0;

    $display("Resetting");
    riscv_dbg.reset_master();

    /// Test ID Code.
    $display("Reading ID Code");
    riscv_dbg.get_idcode(idcode);

    $display("Got ID Code %h", idcode);

    // Check ID Code.
    `ifdef TARGET_BSCANE
    assert(idcode == i_jtag_sime2.IDCODEval_sig);
    `else
    assert(idcode == IDCode);
    `endif

    /// Test DTMCs
    riscv_dbg.read_dtmcs(dtmcs);
    $display("DTMCS: %p", dtmcs);
    assert(dtmcs.version == 1);
    assert(dtmcs.abits == 7);

    riscv_dbg.write_dtmcs(32'hdeadbeef);

    riscv_dbg.read_dtmcs(dtmcs);
    $display("DTMCS: %p", dtmcs);
    assert(dtmcs.version == 1);
    assert(dtmcs.abits == 7);

    /// Random DMI transactions.
    // Generate a number of random transactions and drive them on the JTAG
    // interface.
    start_rand = 1;
    for (int i = 0; i < NrRandomTransactions; i++) begin
      automatic dmi_test::req_t transaction = new;
      assert(transaction.randomize() with {
        op inside {dm::DTM_WRITE, dm::DTM_READ};
      });
      if (transaction.op == dm::DTM_WRITE) begin
        req_mbx.put(transaction);
        riscv_dbg.write_dmi(dm::dm_csr_e'(transaction.addr), transaction.data);
        rsp_mbx.put('h0);
      end else if (transaction.op == dm::DTM_READ) begin
        automatic logic [31:0] rdata;
        req_mbx.put(transaction);
        riscv_dbg.read_dmi(dm::dm_csr_e'(transaction.addr), rdata);
        rsp_mbx.put(rdata);
      end
      // Randomly reset the dmi using either hard jtag trst_ni, JTAG
      // TestLogicReset or the dtmcs.dmihardreset bit.
      if ($urandom_range(0,100) < 5) begin
        riscv_dbg.wait_idle(30);
        case ($urandom_range(0,3))
          0: begin
            $info("Resetting JTAG DMI using asynchronous JTAG reset signal...");
            riscv_dbg.reset_master();
          end

          1: begin
            $info("Resetting JTAG DMI using JTAG softreset (TestLogicReset TAP state).");
              riscv_dbg.jtag.soft_reset();
          end

          2: begin
            dm::dtmcs_t dtmcs_value;
            dtmcs_value = '0;
            dtmcs_value.dmihardreset = 1;
            $info("Resetting JTAG DMI using DMI dtmcs registers' dmihardreset control bit.");
            riscv_dbg.write_dtmcs(dtmcs_value);
          end
        endcase
      end
    end
    #1000;
    $finish();
  end

  // ----------
  // Scoreboard
  // ----------
  initial begin
    forever begin
      automatic dmi_test::req_t req, req_mon;
      automatic dmi_test::rsp_t rsp_mon;
      automatic logic [31:0] rsp;

      dmi_monitor.req_mbx.get(req_mon);
      dmi_monitor.rsp_mbx.get(rsp_mon);
      req_mbx.get(req);
      rsp_mbx.get(rsp);
      nr_transactions++;
      assert(req.addr == req_mon.addr) else
        $error("Invalid dmi request. Got address %0x instead of %0x.", req_mon.addr, req.addr);
      assert(req.op == req_mon.op) else
        $error("Invalid dmi request. Got op %0x instead of %0x.", req_mon.op, req.op);;
      if (req.op == dm::DTM_READ) begin
        assert(rsp_mon.data == rsp);
      end else begin
        assert(req.data == req_mon.data);
      end
    end
  end

  final begin
    assert(NrRandomTransactions == nr_transactions) else $error("Remaining transactions.");
  end

endmodule
