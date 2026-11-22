// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An interface that is bound into the top-level of rom_ctrl.
//
// This has handles to all other interfaces used to interact with rom_ctrl (making it easy to use in
// a testbench). To set whether the interface is active, call set_active(). This will update the
// active flag of the sub-interfaces too.
//
// Note: This interface is not parameterised (to make it easier to use in a non-parameterised
// testbench). To communicate with the design into which it is bound, it uses its ports which, in
// turn, handle handshakes with a surrounding rom_ctrl_bound_if.
//
// Using a structure like this, without hierarchical up-references, means that the type of this
// interface ("virtual rom_ctrl_if") is safe to use in an environment, even if no instance is bound
// into the design.
interface rom_ctrl_if (
  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Connected ports of rom_ctrl
  //
  // These are all wires and some are driven by this interface when in active mode

  // Clock and reset. When this interface is active, it drives both.
  inout wire clk,
  inout wire rst_n,

  // Signals for the ROM TileLink interface.
  //
  // When this interface is active, it drives rom_h2d (acting as a host on the bus)
  inout wire tlul_pkg::tl_h2d_t rom_h2d,
  input wire tlul_pkg::tl_d2h_t rom_d2h,

  // Signals for the register TileLink interface.
  //
  // When this interface is active, it drives regs_h2d (acting as a host on the bus)
  inout wire tlul_pkg::tl_h2d_t regs_h2d,
  input wire tlul_pkg::tl_d2h_t regs_d2h,

  // Signals for the (single) alert interface
  //
  // When this interface is active, it drives alert_rx (acting as a prim_alert_receiver)
  inout wire prim_alert_pkg::alert_rx_t alert_rx,
  input wire prim_alert_pkg::alert_tx_t alert_tx,

  // Data sent from rom_ctrl to pwrmgr and keymgr
  input wire rom_ctrl_pkg::pwrmgr_data_t pwrmgr_data,
  input wire rom_ctrl_pkg::keymgr_data_t keymgr_data,

  // Signals for the KMAC app interface
  //
  // When this interface is active, it drives kmac_rsp_data.
  input wire kmac_pkg::app_req_t kmac_req_data,
  inout wire kmac_pkg::app_rsp_t kmac_rsp_data,

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Handshake ports that allow rom_ctrl_bound_if to interact with internals of the design

  // Ports that control an override of the bus rom index. After a posedge of override_bus_rom_idx_o,
  // the rom_ctrl_bound_if in which this interface lies will wait until it sees the next A channel
  // request to the ROM and will then override the address it uses.
  //
  // Once the A channel transaction has been overridden (or reset has been asserted),
  // the value of bus_rom_idx_overridden_i will flip.
  output bit          override_bus_rom_idx_o,
  output int unsigned desired_bus_rom_idx_o,
  input bit           bus_rom_idx_overridden_i,

  // Ports that control an override for sel_bus_qq in the mux between bus accesses and the FSM.
  //
  // After a posedge of override_sel_bus_qq_o, the rom_ctrl_bound_if in which this interface lies
  // will override u_mux.sel_bus_qq with desired_sel_bus_qq_o until the next negedge of the clock or
  // a reset is asserted. It will then flip the value of sel_bus_qq_overridden_i.
  output bit                    override_sel_bus_qq_o,
  output prim_mubi_pkg::mubi4_t desired_sel_bus_qq_o,
  input bit                     sel_bus_qq_overridden_i,

  // Ports that control forcing a signal in the FSM for a cycle to look like KMAC is reporting it
  // has finished a hash. After a posedge of force_kmac_rsp_valid_o, the rom_ctrl_bound_if in which
  // this interface lies will assert kmac_done_i until the next negedge of the clock or a reset is
  // asserted. It will then flip the value of kmac_rsp_valid_forced_i.
  output bit force_kmac_rsp_valid_o,
  input bit  kmac_rsp_valid_forced_i
);

  clk_rst_if u_clk_rst_if(.clk, .rst_n);

  // Passive clk_rst_vif for second RAL. This consumes the clock/reset signals (possibly driven from
  // outside and possibly driven by u_clk_rst_if). Its signals are only used by the register layer.
  clk_rst_if u_rom_clk_rst_if(.clk, .rst_n);

  // A TileLink interface for access to the ROM.
  tl_if u_tl_rom_if(.clk, .rst_n);

  assign u_tl_rom_if.d2h = rom_d2h;
  assign rom_h2d = u_tl_rom_if.h2d;

  // A TileLink interface for access to registers.
  tl_if u_tl_regs_if(.clk, .rst_n);

  assign u_tl_regs_if.d2h = regs_d2h;
  assign regs_h2d = u_tl_regs_if.h2d;

  // The alert interface for the single alert.
  alert_if u_alert_if (.clk, .rst_n);
  assign u_alert_if.alert_tx = alert_tx;
  assign alert_rx = u_alert_if.alert_rx;

  // The app interface with which rom_ctrl communicates with KMAC
  kmac_app_if u_kmac_app_if(
    .clk_i (clk),
    .rst_ni(rst_n),
    .req   (kmac_req_data),
    .rsp   (kmac_rsp_data)
  );

  function void set_active(bit is_active);
    import dv_utils_pkg::Host, dv_utils_pkg::Device, dv_utils_pkg::Monitor;

    u_clk_rst_if.set_active(.drive_clk_val(is_active), .drive_rst_n_val(is_active));

    // rom_ctrl never acts as a TileLink host. As such, the interface connected to its TL ports
    // should always be either an active host or a monitor.
    u_tl_rom_if.if_mode = is_active ? Host : Monitor;
    u_tl_rom_if.if_mode = is_active ? Host : Monitor;

    // rom_ctrl initiates transaction with KMAC, so acts as a host. As such, the kmap_app_if should
    // either be an active device or a monitor.
    u_kmac_app_if.if_mode = is_active ? Device : Monitor;
  endfunction

  initial begin
    // u_rom_clk_rst_if is always passive (it just consumes clk and rst_n).
    u_rom_clk_rst_if.set_active(0, 0);
  end

  clocking cb @(posedge clk);
    input pwrmgr_data;
    input keymgr_data;
  endclocking

  import uvm_pkg::*;

  // Use the given value to override the next request that comes out of u_tl_adapter_rom. This means
  // that operation will end up asking for the given word instead of the one it expected.
  //
  // The override lasts until the A channel valid signal drops again or reset is asserted.
  task static override_bus_rom_index(int unsigned index);
    if (override_bus_rom_idx_o) begin
      `uvm_fatal($sformatf("%m"), "Overlapping calls that override bus_rom_idx.")
    end

    desired_bus_rom_idx_o  = index;
    override_bus_rom_idx_o = 1;
    @(bus_rom_idx_overridden_i);
    override_bus_rom_idx_o = 0;
  endtask

  // Override the sel_bus_qq index that is used in the mux (between bus accesses and the FSM).
  //
  // Return on the next negedge, giving one cycle if we start before the posedge. Return early on a
  // reset if one is asserted.
  task static override_sel_bus_qq(prim_mubi_pkg::mubi4_t value);
    if (override_sel_bus_qq_o) begin
      `uvm_fatal($sformatf("%m"), "Overlapping calls that override sel_bus_qq.")
    end

    desired_sel_bus_qq_o  = value;
    override_sel_bus_qq_o = 1;
    @(sel_bus_qq_overridden_i);
    override_sel_bus_qq_o = 0;
  endtask

  // Override a signal as if kmac_data_i.rsp_valid signal was true for a cycle.
  //
  // Return on the next negedge, giving one cycle if we start before the posedge. Return early on a
  // reset if one is asserted.
  //
  // Note that this doesn't actually override rom_ctrl's input port, so some sequences that work by
  // monitoring that signal won't see the response.
  task static force_kmac_data_done();
    if (force_kmac_rsp_valid_o) begin
      `uvm_fatal($sformatf("%m"), "Overlapping calls that force rsp_valid_i.")
    end
    force_kmac_rsp_valid_o = 1;
    @(kmac_rsp_valid_forced_i);
    force_kmac_rsp_valid_o = 0;
  endtask

  default disable iff !rst_n;
  default clocking @(posedge clk); endclocking

  // Only get one KMAC response
  //
  // The basic assertion (rsp_valid |=> always(!rsp_valid)) won't complete. To avoid this causing a
  // coverage hole, we register the fact that we've seen rsp_valid since the last reset and assert a
  // property that only lasts a cycle: seen_rsp_valid |-> !rsp_valid.
  bit seen_rsp_valid;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      seen_rsp_valid <= 1'b0;
    end else begin
      seen_rsp_valid <= seen_rsp_valid | kmac_rsp_data.rsp_valid;
    end
  end
  JustOneKmacResponse_A:
    assert property (seen_rsp_valid |-> !kmac_rsp_data.rsp_valid)
    else `ASSERT_ERROR(JustOneKmacResponse_A)

  // Once we signal done to pwrmgr, the done signal stays high and the good signal stays stable.
  //
  // To avoid an "always" in the property (like with JustOneKmacResponse_A), we register the fact
  // that we have seen pwrmgr_data.done be MuBi4True and then assert stability of pwrmgr_data (which
  // contains both done and good).
  bit seen_done;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      seen_done <= 1'b0;
    end else begin
      seen_done <= seen_done | (pwrmgr_data.done == prim_mubi_pkg::MuBi4True);
    end
  end
  PwrmgrDoneOneWay_A:
    assert property (seen_done |-> $stable(pwrmgr_data))
    else `ASSERT_ERROR(PwrmgrDoneOneWay_A)

  // Don't send any KMAC requests once we've had the response
  //
  // As with the previous assertions, we avoid an "always" in the property by registering the fact
  // that we've seen a KMAC response.
  bit seen_kmac_rsp;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      seen_kmac_rsp <= 1'b0;
    end else begin
      seen_kmac_rsp <= seen_kmac_rsp | kmac_rsp_data.rsp_valid;
    end
  end

  KmacNotOutAfterIn_A:
    assert property (seen_kmac_rsp |-> !kmac_req_data.req_valid)
    else `ASSERT_ERROR(KmacNotOutAfterIn_A)

  // We see a response from KMAC before we assert that we're done to pwrmgr
  //
  // This is specified with |=> to allow us to check the (registered) seen_kmac_rsp signal.
  KmacResponseBeforePwmgrDone_A:
    assert property (pwrmgr_data.done != prim_mubi_pkg::MuBi4False |=> seen_kmac_rsp)
    else `ASSERT_ERROR(KmacResponseBeforePwmgrDone_A)
endinterface
