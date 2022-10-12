// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Florian Zaruba <zarubaf@iis.ee.ethz.ch>

/// A set of testbench utilities for the DMI interfaces.
package dmi_test;

  import dm::*;

  class req_t #(
    parameter int AW = 7
  );
    rand logic [AW-1:0] addr;
    rand dtm_op_e       op;
    rand logic [31:0]   data;

    /// Compare objects of same type.
    function do_compare(req_t rhs);
      return addr == rhs.addr &
             op == rhs.op &
             data == rhs.data;
    endfunction

  endclass

  class rsp_t;
    rand logic [31:0]   data;
    rand logic [1:0]    resp;

    /// Compare objects of same type.
    function do_compare(rsp_t rhs);
      return data == rhs.data &
             resp == rhs.resp;
    endfunction

  endclass

  /// A driver for the DMI interface.
  class dmi_driver #(
    parameter int  AW = -1,
    parameter time TA = 0 , // stimuli application time
    parameter time TT = 0   // stimuli test time
  );
    virtual DMI_BUS_DV #(
      .ADDR_WIDTH(AW)
    ) bus;

    function new(
      virtual DMI_BUS_DV #(
        .ADDR_WIDTH(AW)
      ) bus
    );
      this.bus = bus;
    endfunction

    task reset_master;
      bus.q_addr  <= '0;
      bus.q_op    <= DTM_NOP;
      bus.q_data  <= '0;
      bus.q_valid <= '0;
      bus.p_ready <= '0;
    endtask

    task reset_slave;
      bus.q_ready <= '0;
      bus.p_data  <= '0;
      bus.p_resp  <= '0;
      bus.p_valid <= '0;
    endtask

    task cycle_start;
      #TT;
    endtask

    task cycle_end;
      @(posedge bus.clk_i);
    endtask

    /// Send a request.
    task send_req (input req_t req);
      bus.q_addr  <= #TA req.addr;
      bus.q_op    <= #TA req.op;
      bus.q_data  <= #TA req.data;
      bus.q_valid <= #TA 1;
      cycle_start();
      while (bus.q_ready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      bus.q_addr  <= #TA '0;
      bus.q_op    <= #TA DTM_NOP;
      bus.q_data  <= #TA '0;
      bus.q_valid <= #TA 0;
    endtask

    /// Send a response.
    task send_rsp (input rsp_t rsp);
      bus.p_data  <= #TA rsp.data;
      bus.p_resp   <= #TA rsp.resp;
      bus.p_valid <= #TA 1;
      cycle_start();
      while (bus.p_ready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      bus.p_data  <= #TA '0;
      bus.p_resp  <= #TA '0;
      bus.p_valid <= #TA 0;
    endtask

    /// Receive a request.
    task recv_req (output req_t req);
      bus.q_ready <= #TA 1;
      cycle_start();
      while (bus.q_valid != 1) begin cycle_end(); cycle_start(); end
      req = new;
      req.addr  = bus.q_addr;
      req.op    = bus.q_op;
      req.data  = bus.q_data;
      cycle_end();
      bus.q_ready <= #TA 0;
    endtask

    /// Receive a response.
    task recv_rsp (output rsp_t rsp);
      bus.p_ready <= #TA 1;
      cycle_start();
      while (bus.p_valid != 1) begin cycle_end(); cycle_start(); end
      rsp = new;
      rsp.data  = bus.p_data;
      rsp.resp = bus.p_resp;
      cycle_end();
      bus.p_ready <= #TA 0;
    endtask

    /// Monitor request.
    task mon_req (output req_t req);
      cycle_start();
      while (!(bus.q_valid && bus.q_ready)) begin cycle_end(); cycle_start(); end
      req = new;
      req.addr  = bus.q_addr;
      req.op    = bus.q_op;
      req.data  = bus.q_data;
      cycle_end();
    endtask

    /// Monitor response.
    task mon_rsp (output rsp_t rsp);
      cycle_start();
      while (!(bus.p_valid && bus.p_ready)) begin cycle_end(); cycle_start(); end
      rsp = new;
      rsp.data  = bus.p_data;
      rsp.resp = bus.p_resp;
      cycle_end();
    endtask

  endclass

  // Super class for random dmi drivers.
  virtual class rand_dmi #(
    // dmi interface parameters
    parameter int   AW = 32,
    // Stimuli application and test time
    parameter time  TA = 0ps,
    parameter time  TT = 0ps
  );

    typedef dmi_test::dmi_driver #(
      // dmi bus interface parameters;
      .AW ( AW ),
      // Stimuli application and test time
      .TA ( TA ),
      .TT ( TT )
    ) dmi_driver_t;

    dmi_driver_t drv;

    function new(virtual DMI_BUS_DV #( .ADDR_WIDTH (AW)) bus);
      this.drv = new (bus);
    endfunction

    task automatic rand_wait(input int unsigned min, input int unsigned max);
      int unsigned rand_success, cycles;
      rand_success = std::randomize(cycles) with {
        cycles >= min;
        cycles <= max;
        // Weigh the distribution so that the minimum cycle time is the common
        // case.
        cycles dist {min := 10, [min+1:max] := 1};
      };
      assert (rand_success) else $error("Failed to randomize wait cycles!");
      repeat (cycles) @(posedge this.drv.bus.clk_i);
    endtask

  endclass

  /// Generate random requests as a master device.
  class rand_dmi_master #(
    // dmi interface parameters
    parameter int   AW = 32,
    // Stimuli application and test time
    parameter time  TA = 0ps,
    parameter time  TT = 0ps,
    parameter int unsigned REQ_MIN_WAIT_CYCLES = 1,
    parameter int unsigned REQ_MAX_WAIT_CYCLES = 20,
    parameter int unsigned RSP_MIN_WAIT_CYCLES = 1,
    parameter int unsigned RSP_MAX_WAIT_CYCLES = 20
  ) extends rand_dmi #(.AW(AW), .TA(TA), .TT(TT));

    int unsigned cnt = 0;
    bit req_done = 0;

    /// Reset the driver.
    task reset();
      drv.reset_master();
    endtask

    /// Constructor.
    function new(virtual DMI_BUS_DV #( .ADDR_WIDTH (AW)) bus);
      super.new(bus);
    endfunction

    task run(input int n);
      fork
        send_requests(n);
        recv_response();
      join
    endtask

    /// Send random requests.
    task send_requests (input int n);
      automatic req_t r = new;

      repeat (n) begin
        this.cnt++;
        assert(r.randomize());
        rand_wait(REQ_MIN_WAIT_CYCLES, REQ_MAX_WAIT_CYCLES);
        this.drv.send_req(r);
      end
      this.req_done = 1;
    endtask

    /// Receive random responses.
    task recv_response;
      while (!this.req_done || this.cnt > 0) begin
        automatic rsp_t rsp;
        this.cnt--;
        rand_wait(RSP_MIN_WAIT_CYCLES, RSP_MAX_WAIT_CYCLES);
        this.drv.recv_rsp(rsp);
      end
    endtask
  endclass

  class rand_dmi_slave #(
    // dmi interface parameters
    parameter int   AW = 32,
    // Stimuli application and test time
    parameter time  TA = 0ps,
    parameter time  TT = 0ps,
    parameter int unsigned REQ_MIN_WAIT_CYCLES = 0,
    parameter int unsigned REQ_MAX_WAIT_CYCLES = 10,
    parameter int unsigned RSP_MIN_WAIT_CYCLES = 0,
    parameter int unsigned RSP_MAX_WAIT_CYCLES = 10
  ) extends rand_dmi #(.AW(AW), .TA(TA), .TT(TT));

    mailbox req_mbx = new();

    /// Reset the driver.
    task reset();
      drv.reset_slave();
    endtask

    task run();
      fork
        recv_requests();
        send_responses();
      join
    endtask

    /// Constructor.
    function new(virtual DMI_BUS_DV #( .ADDR_WIDTH (AW)) bus);
      super.new(bus);
    endfunction

    task recv_requests();
      forever begin
        automatic req_t req;
        rand_wait(REQ_MIN_WAIT_CYCLES, REQ_MAX_WAIT_CYCLES);
        this.drv.recv_req(req);
        req_mbx.put(req);
      end
    endtask

    task send_responses();
      automatic rsp_t rsp = new;
      automatic req_t req;
      forever begin
        req_mbx.get(req);
        assert(rsp.randomize());
        @(posedge this.drv.bus.clk_i);
        rand_wait(RSP_MIN_WAIT_CYCLES, RSP_MAX_WAIT_CYCLES);
        this.drv.send_rsp(rsp);
      end
    endtask
  endclass

  class dmi_monitor #(
    // dmi interface parameters
    parameter int   AW = 32,
    // Stimuli application and test time
    parameter time  TA = 0ps,
    parameter time  TT = 0ps
  ) extends rand_dmi #(.AW(AW), .TA(TA), .TT(TT));

    mailbox req_mbx = new, rsp_mbx = new;

    /// Constructor.
    function new(virtual DMI_BUS_DV #( .ADDR_WIDTH (AW)) bus);
      super.new(bus);
    endfunction

    // dmi Monitor.
    task monitor;
      fork
        forever begin
          automatic dmi_test::req_t req;
          this.drv.mon_req(req);
          req_mbx.put(req);
        end
        forever begin
          automatic dmi_test::rsp_t rsp;
          this.drv.mon_rsp(rsp);
          rsp_mbx.put(rsp);
        end
      join
    endtask
  endclass

endpackage