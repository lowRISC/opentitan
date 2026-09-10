// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An interface that is designed to be bound into a rom_ctrl_fsm instance called "u_checker_fsm".
// This can then cleanly access internal information from the fsm.
//
// The "u_checker_fsm" name below works around parameters: the rom_ctrl_fsm module is actually
// parameterised in the depth of ROM and the number of words at the top to use as an expected
// digest. As such, it's much easier to do an upwards hierarchical reference by the name of the
// instance.
//
// This interface is connected to the environment through u_fsm_if, an instance of rom_ctrl_fsm_if
// that is instantiated inside it. This interface is not parameterised and doesn't use any
// hierarchical references, so is safe to use in an environment.
//
// The Bound parameter is passed with a value of 1 whenever this interface is bound into the design
// and everything inside the interface that uses hierarchical references is in a generate block that
// depends on it. This avoids elaboration-time errors from the EDA tool if we don't happen to
// instantiate the interface anywhere.

interface rom_ctrl_fsm_bound_if #(
  parameter bit Bound=0,
  parameter int TopCount=0
) (
  input wire clk_i,
  input wire rst_ni
);
  if (Bound) begin : gen_bound
    // Override the count in u_counter. This happens when override_counter has a posedge. The addr_d
    // signal will be overriden with (the low bits of) desired_counter for one cycle, stopping early
    // on reset, and then counter_overridden will flip.
    //
    // To make the change easier to see in waves, we expect this task to be called at the negedge of
    // the clock (so the forced signal changes at a surprising time) and will hold the forced signal
    // until the negedge after addr_q changes.
    //
    // If reset is applied, release the force and return immediately.
    bit        override_counter;
    bit [31:0] desired_counter;
    bit        counter_overridden;

    initial begin
      counter_overridden = 0;
      forever begin
        wait(override_counter);

        // This implementation would like to work by forcing addr_d. This will only be consumed the
        // next time "go" is asserted, and the force will redirect the address to which we jump. Of
        // course, this doesn't work after the ROM read is complete: go will not be asserted.
        //
        // In this situation, it's less important that we make the fetched word line up correctly:
        // nothing will be fetched anyway, and we just want to stimulate a fault injection check.

        if (!u_checker_fsm.u_counter.done_q) begin
          // This is the standard case, where rom_ctrl is reading through ROM and we want to force
          // addr_d.
          force u_checker_fsm.u_counter.addr_d = desired_counter;

          fork : isolation_fork0 begin
            fork
              begin
                @(u_checker_fsm.u_counter.addr_q);
                @(negedge clk_i);
              end
              wait (!rst_ni);
            join_any
            disable fork;
          end join

          release u_checker_fsm.u_counter.addr_d;
        end else begin
          // This is the "fault injection case": rom_ctrl has read the contents of ROM at this
          // point, so we just want addr_q to change.

          force u_checker_fsm.u_counter.addr_q = desired_counter;

          fork : isolation_fork1 begin
            fork
              @(negedge clk_i);
              wait (!rst_ni);
            join_any
            disable fork;
          end join

          release u_checker_fsm.u_counter.addr_q;
        end

        counter_overridden ^= 1;
        wait(!override_counter);
      end
    end

    // Override the count in u_counter. This is like the override_counter mechanism above, except
    // this works by forcing addr_q instead of addr_d.
    //
    // To make the change easier to see in waves, we expect this task to be called at the negedge of
    // the clock (so addr_d changes at a surprising time) and will hold the forced signal until the
    // next negedge.
    //
    // If reset is applied, release the force and return immediately.
    bit        override_addr_q;
    bit [31:0] desired_addr_q;
    bit        addr_q_overridden;

    initial begin
      addr_q_overridden = 0;
      forever begin
        wait(override_addr_q);

        force u_checker_fsm.u_counter.addr_q = desired_addr_q;

        wait_n_clk_or_rst();

        release u_checker_fsm.u_counter.addr_q;
        addr_q_overridden ^= 1;

        wait(!override_addr_q);
      end
    end

    // Override the the rom_select_bus_o output port from the FSM. This happens when
    // override_select_bus has a posedge. The select_bus_o_overridden signal will be overriden with
    // desired_select_bus for one cycle, stopping early on reset, and then select_bus_o_overridden
    // will flip.
    //
    // If reset is applied, release the force and return immediately.
    bit       override_select_bus;
    bit [3:0] desired_select_bus;
    bit       select_bus_o_overridden;

    initial begin
      select_bus_o_overridden = 0;
      forever begin
        wait(override_select_bus);

        force u_checker_fsm.rom_select_bus_o = prim_mubi_pkg::mubi4_t'(desired_select_bus);
        wait_n_clk_or_rst();
        release u_checker_fsm.rom_select_bus_o;
        select_bus_o_overridden ^= 1;

        wait(!override_select_bus);
      end
    end

    // Override the digest that comes back from KMAC.
    //
    //  1. The override is started by a posedge on override_kmac_digest
    //
    //  2. The code will then wait until u_checker_fsm.kmac_done_i is high (reporting that the
    //     digest has been calculated).
    //
    //  3. It will then start to force u_checker_fsm.kmac_digest_i.
    //
    //  4. The forcing lasts for a cycle, after which the digest has been registered in rom_ctrl's
    //     CSRs.
    //
    //  5. At this point, the code releases u_checker_fsm.kmac_digest_i (if it was forced) and
    //     changes the value of kmac_digest_overridden.
    //
    // If either a reset is asserted or override_kmac_digest drops again during steps 3 or 4, the
    // code will jump straight to step 5.

    bit                            override_kmac_digest;
    bit [kmac_pkg::AppDigestW-1:0] desired_kmac_digest;
    bit                            kmac_digest_overridden;

    initial begin
      kmac_digest_overridden = 0;
      forever begin
        automatic bit is_forcing;

        wait(override_kmac_digest);

        fork : isolation_fork begin
          fork
            wait (!rst_ni);
            wait (!override_kmac_digest);
            begin
              wait(u_checker_fsm.kmac_done_i);
              is_forcing = 1;
              force u_checker_fsm.kmac_digest_i = (TopCount * 32)'(desired_kmac_digest);
              @(posedge clk_i);
            end
          join_any
          disable fork;
        end join

        if (is_forcing) release u_checker_fsm.kmac_digest_i;

        kmac_digest_overridden ^= 1;

        wait(!override_kmac_digest);
      end
    end

    // If force_checker_done sees a posedge, force the checker_done signal to be true for a cycle
    // (or until reset). Once that has happened, flip the value of checker_done_forced.
    bit force_checker_done;
    bit checker_done_forced;

    initial begin
      checker_done_forced = 0;
      forever begin
        wait(force_checker_done);

        force u_checker_fsm.checker_done = 1'b1;
        wait_n_clk_or_rst();
        release u_checker_fsm.checker_done;
        checker_done_forced ^= 1;

        wait(!force_checker_done);
      end
    end

    // If force_counter_done sees a posedge, force the counter_done signal to be true for a cycle
    // (or until reset). Once that has happened, flip the value of counter_done_forced.
    bit force_counter_done;
    bit counter_done_forced;

    initial begin
      counter_done_forced = 0;
      forever begin
        wait(force_counter_done);

        force u_checker_fsm.counter_done = 1'b1;
        wait_n_clk_or_rst();
        release u_checker_fsm.counter_done;
        counter_done_forced ^= 1;

        wait(!force_counter_done);
      end
    end

    // If force_checker_start sees a posedge, force the checker_start signal to be true for a cycle
    // (or until reset). Once that has happened, flip the value of checker_start_forced.
    bit force_checker_start;
    bit checker_start_forced;

    initial begin
      checker_start_forced = 0;
      forever begin
        wait(force_checker_start);

        force u_checker_fsm.start_checker_q = 1'b1;
        wait_n_clk_or_rst();
        release u_checker_fsm.start_checker_q;
        checker_start_forced ^= 1;

        wait(!force_checker_start);
      end
    end

    // Wait for a single negative edge of the clock, returning early if a reset is asserted.
    task static wait_n_clk_or_rst();
      fork : isolation_fork begin
        fork
          @(negedge clk_i);
          wait(!rst_ni);
        join_any
        disable fork;
      end join
    endtask

    rom_ctrl_fsm_if u_fsm_if (
      .clk_i          (clk_i),
      .rst_ni         (rst_ni),
      .fsm_state_i    (u_checker_fsm.state_q),
      .counter_addr_i (32'(u_checker_fsm.u_counter.addr_q)),

      .override_counter_o     (override_counter),
      .desired_counter_o      (desired_counter),
      .counter_o_overridden_i (counter_overridden),

      .override_addr_q_o   (override_addr_q),
      .desired_addr_q_o    (desired_addr_q),
      .addr_q_overridden_i (addr_q_overridden),

      .override_select_bus_o     (override_select_bus),
      .desired_select_bus_o      (desired_select_bus),
      .select_bus_o_overridden_i (select_bus_o_overridden),

      .override_kmac_digest_o   (override_kmac_digest),
      .desired_kmac_digest_o    (desired_kmac_digest),
      .kmac_digest_overridden_i (kmac_digest_overridden),

      .force_checker_done_o (force_checker_done),
      .checker_done_forced_i (checker_done_forced),

      .force_counter_done_o (force_counter_done),
      .counter_done_forced_i (counter_done_forced),

      .force_checker_start_o (force_checker_start),
      .checker_start_forced_i (checker_start_forced)
    );
  end
endinterface
