// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A virtual sequence that will run forever or until abort() is called. It will start a
// rom_ctrl_skip_middle_seq and a rom_ctrl_override_digest_seq after every reset, causing rom_ctrl
// not to send the entirety of ROM to KMAC, but to override the digest that comes back to pretend
// that the hash was as expected.
//
// To use this:
//
//   - Call set_reset_event(), so that the virtual sequence can track resets.
//
//   - Call set_sequencers(), so that the virtual sequence can override the address and the digest
//     response from kmac.
//
//   - Start the sequence itself at the start of the test (before the design leaves its initial
//     reset)

class rom_ctrl_skip_middle_with_digest_vseq extends uvm_sequence;
  `uvm_object_utils(rom_ctrl_skip_middle_with_digest_vseq)

  // The address from which to start the skip (so addr_d will be forced to a higher value when
  // addr_q equals this value).
  rand int unsigned m_start_addr;

  // The address to which we should skip (the forced value of addr_d).
  rand int unsigned m_desired_addr;

  // The digest to use when forcing the response from KMAC (not in shares: this is s0 ^ s1)
  rand bit [kmac_pkg::AppDigestW-1:0] m_digest;

  // A flag that causes this virtual sequence to ask all child sequences to abort and then to drop
  // out of the forever loop.
  local bit m_seen_abort;

  // An event that is triggered when the block changes reset state (either entering or leaving
  // reset). The body() task watches this event and maintains the m_in_reset state variable.
  //
  // Each time the event is triggered comes with a reset_edge_item that gives the new state of the
  // reset line.
  local uvm_event m_reset_event;

  // A state variable that is maintained by the body() task by watching m_reset_event.
  local bit m_in_reset;

  // A state variable that is set the first time track_resets sees an edge (so that m_in_reset is
  // now in sync with the design)
  local bit m_seen_reset_edge;

  // The sequencer to use for the rom_ctrl_skip_middle_seq. Set this with the first argument to
  // set_sequencers.
  local rom_ctrl_addr_force_sequencer_t m_addr_force_sequencer;

  // The sequencer to use for the rom_ctrl_override_digest_seq. Set this with the second argument to
  // set_sequencers.
  local rom_ctrl_kmac_rsp_force_sequencer_t m_kmac_rsp_force_sequencer;

  // A sequence that is currently running and will force the digest in the next KMAC response.
  local rom_ctrl_override_digest_seq m_current_digest_seq;

  extern function new(string name="");

  // Set a handle to the reset event that the sequence should track. This event should be triggered
  // on each change of reset state and the associated data should equal the new value of the rst_n
  // line.
  //
  // Call this before starting the sequence.
  extern function void set_reset_event(uvm_event reset_event);

  // Set the sequencers on which sequences should be run to override the ROM address (in order to
  // skip the middle) and to override the data of the response sent from KMAC (so that rom_ctrl can
  // be provided with the digest it expects).
  //
  // Call this before starting the sequence.
  extern function void set_sequencers(rom_ctrl_addr_force_sequencer_t     addr_sequencer,
                                      rom_ctrl_kmac_rsp_force_sequencer_t rsp_sequencer);

  extern task pre_start();
  extern task body();

  // Stop any running sequence and tell the main sequence to run to completion.
  extern function void abort();

  // Update the value of m_digest with the argument
  //
  // This should not be called when an an instance of rom_ctrl_override_digest_seq is running
  // (because the driver for the item sent by that sequence doesn't know how to update the
  // overridden value). If that sequence is running, this function will fail with an error.
  //
  // To ensure that rom_ctrl_override_digest_seq is not running, call this function when the block
  // is in reset.
  extern function void update_digest(bit [kmac_pkg::AppDigestW-1:0] digest);

  // Watch m_reset_event and keep m_in_reset up to date.
  extern local task track_resets();

  // Create and run a rom_ctrl_addr_force_item that will skip rom_ctrl's read of the middle of ROM.
  // This will run until the skip is complete, or until reset is asserted if that happens first.
  extern local task skip_middle();

  // Force the value of the next response from kmac. This will run until the force is complete, or
  // until reset is asserted if that happens first.
  extern local task force_response();
endclass

function rom_ctrl_skip_middle_with_digest_vseq::new(string name="");
  super.new(name);
endfunction

function void rom_ctrl_skip_middle_with_digest_vseq::set_reset_event(uvm_event reset_event);
  m_reset_event = reset_event;
endfunction

function void
  rom_ctrl_skip_middle_with_digest_vseq::
  set_sequencers(rom_ctrl_addr_force_sequencer_t     addr_sequencer,
                 rom_ctrl_kmac_rsp_force_sequencer_t rsp_sequencer);

  m_addr_force_sequencer     = addr_sequencer;
  m_kmac_rsp_force_sequencer = rsp_sequencer;
endfunction

task rom_ctrl_skip_middle_with_digest_vseq::pre_start();
  super.pre_start();

  if (m_reset_event == null)
    `uvm_fatal(get_full_name(), "No reset_event provided.")

  if (m_addr_force_sequencer == null)
    `uvm_fatal(get_full_name(), "No addr_sequencer provided.")

  if (m_kmac_rsp_force_sequencer == null)
    `uvm_fatal(get_full_name(), "No rsp_sequencer provided.")
endtask

task rom_ctrl_skip_middle_with_digest_vseq::body();
  fork
    track_resets();
    while(!m_seen_abort) begin
      bit middle_skipped, rsp_forced;

      // Wait until we know that we are not in reset. If m_seen_reset_edge is true, we are tracking
      // the current reset state. This means that m_in_reset is correct, so we just need to wait
      // until it's false.
      //
      // Note that this sequence will probably be run at the start of the simulation, and might or
      // might not see a time zero event where rst_n gets its initial value. This doesn't matter
      // though: we want to wait until the block *leaves* reset, which will be a few cycles later.
      //
      // Drop out early if m_seen_abort becomes true.
      wait((m_seen_reset_edge && !m_in_reset) || m_seen_abort);
      if (m_seen_abort) continue;

      `uvm_info(get_full_name(),
                {"At end of reset. Starting sequences to skip the middle of ROM ",
                 "and override the response from KMAC."},
                UVM_HIGH)

      fork : isolation_fork begin
        // Try to skip the middle of ROM and force the response that comes back from KMAC. The first
        // process waits for both of these things to happen.
        //
        // Drop out early if a reset is asserted and cleared again. This shouldn't ever be the
        // process that causes the fork to end (because skip_middle and force_response should both
        // have completed when the reset was asserted), but it gives us a chance to spot that
        // something has come unstuck.
        fork
          begin
            wait(middle_skipped && rsp_forced);
          end
          begin
            skip_middle();
            middle_skipped = 1;
            wait(0);
          end
          begin
            force_response();
            rsp_forced = 1;
            wait(0);
          end
          begin
            wait(m_in_reset);
            wait(!m_in_reset);
          end
        join_any

        // At this point, the skip_middle task has been started. In the normal case, we'd expect
        // this to run to completion (skipping the middle of the ROM) and then set middle_skipped.
        //
        // If a reset has been asserted, we still expect skip_middle to run to completion: it's
        // supposed to drop out immediately. Make sure that this happens.
        if (!middle_skipped) begin
          `uvm_fatal(get_full_name(), "A reset was asserted and ended again before skip_middle.")
        end

        // Similarly, the force_response has been started and should have returned, causing us to
        // set rsp_forced=1. Check that this has happened.
        if (!rsp_forced) begin
          `uvm_fatal(get_full_name(), "A reset was asserted and ended again before force_response.")
        end

        // Since middle_skipped and rsp_forced are set, the only processes still running are two
        // wait(0)'s and the one that waits for reset to be asserted and cleared. Disable those
        // here.
        disable fork;
      end join

      // Since skip_middle and force_response ran to completion, we have either not seen a reset at
      // all, or we are in the middle of a reset. Wait until we are in a reset to guarantee we are
      // in the second case.
      //
      // This sequence might have been aborted. In that case, both skip_middle and force_response
      // will have returned quickly and we should stop the loop here. Similarly, we should drop out
      // of the wait statement if the sequence gets aborted while we're waiting.
      wait(m_in_reset || m_seen_abort);
    end
  join
endtask

function void rom_ctrl_skip_middle_with_digest_vseq::abort();
  m_seen_abort = 1;
endfunction

function void
  rom_ctrl_skip_middle_with_digest_vseq::update_digest(bit [kmac_pkg::AppDigestW-1:0] digest);

  if (m_current_digest_seq != null) begin
    `uvm_fatal(get_full_name(), "There is already a digest override sequence running.")
  end

  m_digest = digest;
endfunction

task rom_ctrl_skip_middle_with_digest_vseq::track_resets();
  forever begin
    uvm_object                       event_item;
    reset_agent_pkg::reset_edge_item edge_item;

    fork : isolation_fork begin
      fork
        m_reset_event.wait_trigger_data(event_item);
        wait(m_seen_abort);
      join_any
      disable fork;
    end join

    if (m_seen_abort) return;

    if (!$cast(edge_item, event_item)) begin
      `uvm_fatal(get_full_name(), "Reset event was triggered with no reset_edge_item attached.")
    end

    // Consistency check: we expect an edge to change the reset state, so should not see the event
    // triggered unless new_rst_n != !m_in_reset.
    if (m_seen_reset_edge && (edge_item.m_new_state == !m_in_reset)) begin
      `uvm_fatal(get_full_name(),
                 $sformatf({"Reset tracking inconsistency. m_in_reset was %0d, corresponding to ",
                            "rst_n=%0d, but m_reset_event was triggered with m_new_state=%0d."},
                           m_in_reset, !m_in_reset, edge_item.m_new_state))
    end

    m_in_reset = !edge_item.m_new_state;
    m_seen_reset_edge = 1;
  end
endtask

task rom_ctrl_skip_middle_with_digest_vseq::skip_middle();
  rom_ctrl_skip_middle_seq seq = rom_ctrl_skip_middle_seq::type_id::create("seq");

  if (!seq.randomize() with {
        m_item.m_start_addr   == local::m_start_addr;
        m_item.m_desired_addr == local::m_desired_addr;
      }) begin
    `uvm_fatal(get_full_name(), "Failed to randomise rom_ctrl_skip_middle_seq.")
  end

  fork : isolation_fork begin
    fork
      seq.start(m_addr_force_sequencer);
      begin
        wait(m_seen_abort);
        seq.abort();
        wait(0);
      end
    join_any
    disable fork;
  end join
endtask

task rom_ctrl_skip_middle_with_digest_vseq::force_response();
  m_current_digest_seq = rom_ctrl_override_digest_seq::type_id::create("m_current_digest_seq");

  if (!m_current_digest_seq.randomize() with {
        m_item.m_digest == local::m_digest;
      }) begin
    `uvm_fatal(get_full_name(), "Failed to randomise rom_ctrl_override_digest_seq.")
  end

  fork : isolation_fork begin
    fork
      m_current_digest_seq.start(m_kmac_rsp_force_sequencer);
      begin
        wait(m_seen_abort);
        m_current_digest_seq.abort();
        wait(0);
      end
    join_any
    disable fork;
  end join

  m_current_digest_seq = null;
endtask
