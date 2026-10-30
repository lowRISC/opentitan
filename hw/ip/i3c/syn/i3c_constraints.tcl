# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# I3C timing constraints, shared by the ASIC (SDC) and the FPGA (XDC) flows.
#
# The I3C IP shares one SCL/SDA pad pair for Controller and Target roles:
#
#  - The Controller is synchronous to clk_i and *generates* SCL. With
#    HalfCycleScl set, SCL is `state_q[ST_SCL] | gen_hc_scl.scl_n`, i.e., a
#    posedge flop OR'ed with a negedge flop (i3c_controller_trx.sv).
#  - The Target has no free-running clock. It is clocked by the bus itself:
#    SCL and its inverse for SDR/HDR-DDR data, SDA and its inverse for
#    START/STOP detection (i3c_input_buffers.sv, four clock trees).
#
# Consequently, each pad carries two mutually exclusive SCL *sources*:
# The self-generated Controller clock, and the one from an external Active
# Controller.
# Important: The Target clock trees are live in either case. Both SCL clocks
# are therefore declared on the pad and made physically exclusive, and both
# propagate into the Target.
#
# Timing is per MIPI I3C Basic v1.2 (+ Errata 01), Tables 48-50 and Figures
# 73/80/81. In SDR, SDA is launched on the falling SCL edge and sampled on the
# rising edge; HDR-DDR uses both edges, so every data constraint is applied to
# both.
#
# Usage:
#   set ::i3c_cfg(reg_q_pin) {q[%d]}       ;# Netlist naming; DC/PT by default
#   set ::i3c_cfg(board_dly_max) 2.0       ;# override any default below
#   source .../i3c_constraints.tcl
#   i3c_pinmux_case_analysis $u_pinmux { {38 38 19} {39 39 18} ... }
#   i3c_constrain $inst IOB10 IOB9 I3C0 $clk_pin $clk_name
#
# All delay values are in nanoseconds.

#############################
# Configuration             #
#############################

if {![info exists ::i3c_cfg]} {
  array set ::i3c_cfg {}
}

# Only set a default if the caller has not already chosen a value.
proc i3c_cfg_default {key value} {
  if {![info exists ::i3c_cfg($key)]} {
    set ::i3c_cfg($key) $value
  }
}

## Bus timing, from the I3C Basic v1.2 specification.
# Table 50: fSCL max 12.9 MHz. This bounds an externally driven SCL; our own
# Controller's SCL is derived from clk_i instead (see i3c_create_clocks).
i3c_cfg_default scl_ext_period 77.5
# Table 50: tSCO, SCL in to SDA out for a Target, max 20 ns. This is our own
# obligation when acting as a Target.
i3c_cfg_default tsco_max 20.0
# What a remote Target may take before it presents read data. Devices slower
# than 20 ns must advertise it in the BCR, so 20 ns is the compliant bound.
i3c_cfg_default tsco_ext_max 20.0
# Table 50: tSU_PP / Table 49: tSU_OD, SDA setup, min 3 ns.
i3c_cfg_default tsu_pp 3.0
# Table 50: tHD_PP, min 0 for a Target, tCR/tCF + 3 ns for a Controller.
i3c_cfg_default thd_pp_tgt 0.0
# Table 50 note 5 caps tCR/tCF at 60 ns; integration_notes.md:62-63 requires
# <= 8 ns to reach the full 12.5 MHz signalling rate.
i3c_cfg_default tcr 8.0
i3c_cfg_default tcf 8.0

## Whether to model the I3C bus I/O timing at all. With this off, only the bus
## clocks, the pinmux case analysis and the internal budgets are applied: the
## logic is still timed, but the interface is not held to the specification.
## Turn it off for a target that physically cannot meet the specification and
## is only used for functional bring-up, such as an FPGA where SCL and SDA run
## through a pinmux.
i3c_cfg_default bus_io_delays 1

## Board and pad delays. Set these to the real numbers for the system.
# Pad-to-pad wiring (t3 and t7 of specification Figure 73).
i3c_cfg_default board_dly_max 2.0
i3c_cfg_default board_dly_min 0.1
# Extra budget for our own pad cells, for flows where the pad is a black box
# without timing. Leave at 0 when STA already models the pad, which is the
# normal case for both a foundry pad library and an FPGA IOBUF.
i3c_cfg_default pad_out_dly_max 0.0
i3c_cfg_default pad_out_dly_min 0.0
i3c_cfg_default pad_in_dly_max 0.0
i3c_cfg_default pad_in_dly_min 0.0

## Controller SCL waveform, in edges of the clk_i source clock.
# i3c_timing_pkg::tm_params() turns the target SCL period (TPERIOD_SDR0 = 80 ns)
# and high interval (TDIGH = 36 ns) into clk_i cycle counts. At ClkFreq = 96 MHz
# this yields tchh=2, tchs=1, hcext=1, tclh=3, tcls=2: an 8 cycle period whose
# high phase is 3.5 cycles, because the half-cycle extension overlaps tclh
# rather than lengthening the period (i3c_timing_pkg.sv).
# Counting source clock transitions, edge 1 is the first rising edge, edge 8 the
# falling edge 3.5 cycles later and edge 17 the rising edge 8 cycles later.
i3c_cfg_default scl_edges {1 8 17}
# clk_i cycles the Controller waits after the SCL edge before sampling SDA. It
# captures at the end of State_ClkLoAwaitD (i3c_controller_trx.sv), the
# clk_i edge on which SCL rises, which is tclh + tcls cycles after SCL fell.
i3c_cfg_default ctrl_rx_cycles 5

## Internal paths.
# Budget for clk_i <-> bus clock domain crossings, as a fraction of the clk_i
# period. Matches what is done in chip_earlgrey_asic_check_only.sdc.
i3c_cfg_default cdc_fraction 0.9
# Allowed skew between the SCL clock tree and the buffered SDA data it samples
# (i3c_input_buffers.sv, TODO #31335), and between the two flops forming the
# Controller's SCL output (integration_notes.md:51).
i3c_cfg_default sda_skew_max 1.0
i3c_cfg_default scl_out_skew_max 1.0
# Window the START/STOP detectors have to resolve a bus condition in. SDA and
# SCL are asynchronous to each other, so these clock-as-data paths get an
# explicit bound rather than a clock relationship. Table 49: tCAS min 38.4 ns,
# tCBP min tCAS/2.
i3c_cfg_default start_stop_max 19.2

## Netlist naming. Vivado names a prim_subreg bit q_reg[N]/Q; DC and PrimeTime
## name the module output pin q[N]. Likewise for the packed pad attribute
## register: mio_pad_attr_q_reg[19][invert] vs mio_pad_attr_q_reg_19__invert.
i3c_cfg_default reg_q_pin {q[%d]}
i3c_cfg_default pad_attr_pin {mio_pad_attr_q_reg_%d__%s/Q}

#############################
# Helpers                   #
#############################

# Apply set_case_analysis to a pin, if it exists. Attribute flops in particular
# are WARL-masked per technology, so some are legitimately absent: on FPGA only
# `invert` survives for a MIO pad. Returns 1 if applied.
proc i3c_case_if_present {value pattern} {
  set pins [get_pins -quiet $pattern]
  if {[llength $pins] == 0} {
    return 0
  }
  set_case_analysis $value $pins
  return 1
}

# Apply set_case_analysis to a pin that must exist, so that a typo is caught
# rather than silently dropping a constraint.
proc i3c_case {value pattern} {
  if {![i3c_case_if_present $value $pattern]} {
    error "i3c_constraints: no such pin: $pattern"
  }
}

# Drive a `width`-bit register to `value`, one bit at a time.
proc i3c_case_reg {base width value} {
  for {set bit 0} {$bit < $width} {incr bit} {
    set pin "${base}/[format $::i3c_cfg(reg_q_pin) $bit]"
    i3c_case [expr {($value >> $bit) & 1}] $pin
  }
}

# True if the running tool provides `cmd`, used to keep this file portable
# between Vivado and the Synopsys tools.
proc i3c_has_command {cmd} {
  return [expr {[llength [info commands $cmd]] > 0}]
}

# Collect leaf pins of the given direction. A pattern that matched a
# hierarchical pin would not be a valid timing start- or endpoint.
proc i3c_pins {pattern direction} {
  return [get_pins -quiet -hierarchical -filter \
      "full_name =~ ${pattern} && DIRECTION == ${direction}"]
}

# Apply a best-effort constraint, warning rather than aborting when the netlist
# does not have the expected structure. Used only for the internal budgets; the
# clocks, the case analysis and the I/O delays must all apply, so a mistake
# there still stops the run.
proc i3c_try {desc script} {
  if {[catch {uplevel 1 $script} err]} {
    puts "i3c_constraints: WARNING: skipped ${desc}: ${err}"
  }
}

#############################
# Pinmux case analysis      #
#############################

# Pin the pinmux selects so that each I3C signal has exactly one pad, in both
# directions, and so no other muxed pad's clock reaches the I3C clock trees.
# This is independent of where the I3C instances sit in the hierarchy.
#
#   pinmux       path to the pinmux instance
#   assignments  list of {periph_in_idx periph_out_idx pad_idx}
#
# Mux encodings (pinmux.sv):
#   mio_mux        = {mio_in, 1'b1, 1'b0}            -> insel  = pad_idx + 2
#   periph_data_mux = {periph_to_mio_i, 0, 1, 0}     -> outsel = periph_out + 3
proc i3c_pinmux_case_analysis {pinmux assignments} {
  set pads {}
  foreach entry $assignments {
    lassign $entry periph_in periph_out pad
    lappend pads $pad

    # Input: the peripheral input reads this pad.
    i3c_case_reg "${pinmux}/u_reg/u_mio_periph_insel_${periph_in}" 6 [expr {$pad + 2}]
    # Output: this pad is driven by the peripheral output.
    i3c_case_reg "${pinmux}/u_reg/u_mio_outsel_${pad}" 7 [expr {$periph_out + 3}]
  }

  foreach pad [lsort -unique -integer $pads] {
    # Take the functional branch of the sleep retention mux in front of the
    # output select (pinmux.sv).
    set sleep_reg [expr {$pad < 32 ? "u_mio_pad_sleep_status_0_en_${pad}"
                                   : "u_mio_pad_sleep_status_1_en_${pad}"}]
    i3c_case_if_present 0 "${pinmux}/u_reg/${sleep_reg}/[format $::i3c_cfg(reg_q_pin) 0]"

    # Pad attributes that would otherwise make the pad non-unate or cut the
    # signal (prim_pad_wrapper.sv):
    #   invert        XORs both the input and the output
    #   virt_od_en    makes the output enable depend on the output data
    #   input_disable turns the input buffer off
    # Which of these exist depends on the technology's WARL mask, so they are
    # applied only where present.
    set applied {}
    foreach attr {invert virt_od_en input_disable} {
      if {[i3c_case_if_present 0 \
               "${pinmux}/[format $::i3c_cfg(pad_attr_pin) $pad $attr]"]} {
        lappend applied $attr
      }
    }
    # Report what was pinned: a silently empty list usually means the attribute
    # naming does not match this tool's netlist, rather than a WARL-masked bit.
    puts "i3c_constraints: MIO pad ${pad} attributes pinned: [join $applied { }]"
  }
}

#############################
# Clocks                    #
#############################

# Create the bus clocks for one I3C instance.
#
#   inst       path to the i3c instance
#   scl_port   chip port carrying SCL
#   sda_port   chip port carrying SDA
#   prefix     clock name prefix, e.g. I3C0
#   clk_pin    pin carrying the IP's clk_i, used as the generated clock source
#   clk_name   name of the clock on clk_pin, used as the master clock
proc i3c_create_clocks {inst scl_port sda_port prefix clk_pin clk_name} {
  # An external Active Controller drives SCL; we are a Target. 12.9 MHz is the
  # Table 50 maximum, including the short bursts caused by jitter and skew.
  create_clock -name ${prefix}_SCL_EXT -period $::i3c_cfg(scl_ext_period) \
      [get_ports $scl_port] -add

  # Our own Controller drives SCL, derived from clk_i. Only one of the two can
  # be driving the pad, so they are physically exclusive. This clock exists to
  # give the Controller's own SDA timing a reference, so it is only needed when
  # the bus I/O timing is modelled.
  if {$::i3c_cfg(bus_io_delays)} {
    create_generated_clock -name ${prefix}_SCL_INT -source [get_pins $clk_pin] \
        -edges $::i3c_cfg(scl_edges) -master_clock [get_clocks $clk_name] \
        [get_ports $scl_port] -add

    set_clock_groups -name ${prefix}_SCL_SRC -physically_exclusive \
        -group [get_clocks ${prefix}_SCL_EXT] \
        -group [get_clocks ${prefix}_SCL_INT]

    # Stop the generated SCL at the pad. It is defined on a bidirectional port,
    # so it would otherwise propagate back in through the pad and clock the
    # Target, which is electrically real on a shared bus but makes the Target
    # a clk_i-related domain reached via a full pad-board-pad round trip. The
    # resulting skew is tens of nanoseconds and breaks both setup and hold.
    # The Target is timed against the externally driven SCL instead.
    i3c_try "stop ${prefix}_SCL_INT at the pad" {
      set tree_in [get_pins -quiet \
          ${inst}/u_core/u_targ_inbufs/u_scl_buf/u_buf/*/I]
      if {[llength $tree_in] && [i3c_has_command set_clock_sense]} {
        set_clock_sense -stop_propagation -clocks [get_clocks ${prefix}_SCL_INT] \
            $tree_in
      } elseif {[llength $tree_in] && [i3c_has_command set_sense]} {
        set_sense -stop_propagation -clocks [get_clocks ${prefix}_SCL_INT] $tree_in
      }
    }
  }

  # SDA clocks the Target's START/STOP detectors (i3c_target_trx.sv).
  # It transitions at most once per SCL half period, so the SCL period bounds
  # it as well.
  create_clock -name ${prefix}_SDA -period $::i3c_cfg(scl_ext_period) \
      [get_ports $sda_port] -add

  # A bus driven from outside has no relationship to anything else in the
  # design. A single-clock group is asynchronous to every other clock, which is
  # what we want for both of these.
  #
  # SCL_INT is deliberately NOT grouped here: it is generated from clk_i and
  # must stay related to it, otherwise the Controller's own output and input
  # paths would be cut. The caller has to add it to the group that holds clk_i
  # (see i3c_scl_int_clock).
  set_clock_groups -name ${prefix}_SCL_EXT_ASYNC -asynchronous \
      -group [get_clocks ${prefix}_SCL_EXT]
  set_clock_groups -name ${prefix}_SDA_ASYNC -asynchronous \
      -group [get_clocks ${prefix}_SDA]
}

# Name of the generated clock that has to join the clk_i clock group at top
# level, because it is derived from clk_i rather than from the bus.
proc i3c_scl_int_clock {prefix} {
  return ${prefix}_SCL_INT
}

#############################
# I/O delays                #
#############################

# Constrain SDA against SCL for one I3C instance, in both roles and on both
# clock edges. The reference point is the chip port, which is where the
# specification defines its timing.
proc i3c_set_io_delays {inst scl_port sda_port prefix clk_name} {
  if {!$::i3c_cfg(bus_io_delays)} {
    puts "i3c_constraints: ${prefix}: bus I/O timing not modelled"
    return
  }
  set sda [get_ports $sda_port]

  # External budget seen from our port, in each direction.
  set out_max [expr {$::i3c_cfg(board_dly_max) + $::i3c_cfg(pad_out_dly_max)}]
  set out_min [expr {$::i3c_cfg(board_dly_min) + $::i3c_cfg(pad_out_dly_min)}]
  set in_max  [expr {$::i3c_cfg(board_dly_max) + $::i3c_cfg(pad_in_dly_max)}]
  set in_min  [expr {$::i3c_cfg(board_dly_min) + $::i3c_cfg(pad_in_dly_min)}]

  # Target role: the bus is driven by an external Active Controller, so the
  # timing is relative to SCL_EXT. When our own Controller drives the bus
  # instead, the interface timing is the Controller case below; SCL_INT still
  # reaches the Target clock trees by propagation, so that logic stays timed
  # either way.
  set scl_clk ${prefix}_SCL_EXT
  set half [expr {$::i3c_cfg(scl_ext_period) / 2.0}]

  ## SDA is launched and sampled by SCL itself.
  #
  # Output. Our tSCO obligation is measured from the SCL edge at the pad, so
  # the required time has to land tSCO after that edge. With the capture edge
  # half a period away, that is an output delay of (half period - tSCO).
  # The board delay is added on top, which tightens our own budget by that
  # amount rather than leaving it to the far end: deliberately conservative,
  # and it costs nothing when board_dly_max is set to the real number.
  # Hold: SDA must not move before tHD_PP, which is 0 for a Target.
  set tgt_out_max [expr {$half - $::i3c_cfg(tsco_max) + $out_max}]
  set tgt_out_min [expr {-1.0 * ($::i3c_cfg(thd_pp_tgt) + $out_min)}]
  # Input. A remote Controller presents SDA tSU_PP before the edge that
  # samples it and holds it tHD_PP = tCF/tCR + 3 ns afterwards.
  set tgt_in_max [expr {$half - $::i3c_cfg(tsu_pp) + $in_max}]
  set tgt_in_min_f [expr {$::i3c_cfg(tcf) + 3.0 + $in_min}]
  set tgt_in_min_r [expr {$::i3c_cfg(tcr) + 3.0 + $in_min}]

  # SDR launches on the falling edge and samples on the rising edge; HDR-DDR
  # uses both, so each constraint is applied against both edges.
  set_output_delay -max $tgt_out_max -clock $scl_clk $sda -add_delay
  set_output_delay -min $tgt_out_min -clock $scl_clk $sda -add_delay
  set_output_delay -max $tgt_out_max -clock $scl_clk -clock_fall $sda -add_delay
  set_output_delay -min $tgt_out_min -clock $scl_clk -clock_fall $sda -add_delay

  set_input_delay -max $tgt_in_max -clock $scl_clk -clock_fall $sda -add_delay
  set_input_delay -min $tgt_in_min_f -clock $scl_clk -clock_fall $sda -add_delay
  set_input_delay -max $tgt_in_max -clock $scl_clk $sda -add_delay
  set_input_delay -min $tgt_in_min_r -clock $scl_clk $sda -add_delay

  ## Controller role. SDA is launched and captured by clk_i, but the bus timing
  ## is relative to the SCL we generate, so SCL_INT is the reference.
  set scl_clk ${prefix}_SCL_INT
  set half [expr {$::i3c_cfg(scl_ext_period) / 2.0}]

  # Output: the remote Target needs tSU_PP of setup and tHD_PP of hold.
  set ctrl_out_max [expr {$::i3c_cfg(tsu_pp) + $out_max}]
  set ctrl_out_min_f [expr {-1.0 * ($::i3c_cfg(tcf) + 3.0 + $out_min)}]
  set ctrl_out_min_r [expr {-1.0 * ($::i3c_cfg(tcr) + 3.0 + $out_min)}]
  set_output_delay -max $ctrl_out_max -clock $scl_clk $sda -add_delay
  set_output_delay -min $ctrl_out_min_r -clock $scl_clk $sda -add_delay
  set_output_delay -max $ctrl_out_max -clock $scl_clk -clock_fall $sda -add_delay
  set_output_delay -min $ctrl_out_min_f -clock $scl_clk -clock_fall $sda -add_delay

  # Input: a remote Target answers at most tSCO after the SCL edge.
  set ctrl_in_max [expr {$::i3c_cfg(tsco_ext_max) + $in_max}]
  set ctrl_in_min [expr {$::i3c_cfg(thd_pp_tgt) + $in_min}]
  set_input_delay -max $ctrl_in_max -clock $scl_clk -clock_fall $sda -add_delay
  set_input_delay -min $ctrl_in_min -clock $scl_clk -clock_fall $sda -add_delay

  # The Controller samples with clk_i, not with SCL, and deliberately waits
  # until the middle of the SCL low phase (i3c_timing_pkg.sv). Without
  # a multicycle the tool would check against the first clk_i edge after the
  # SCL edge, which no amount of logic could meet.
  set mcp $::i3c_cfg(ctrl_rx_cycles)
  set_multicycle_path -setup $mcp -end -from [get_clocks $scl_clk] \
      -to [get_clocks $clk_name] -through $sda
  set_multicycle_path -hold [expr {$mcp - 1}] -end -from [get_clocks $scl_clk] \
      -to [get_clocks $clk_name] -through $sda
}

#############################
# Internal paths            #
#############################

# Constraints inside one I3C instance: clock-tree structure, bus-to-core
# crossings and the two skew budgets the design relies on.
proc i3c_set_internal_paths {inst clk_name clk_period} {
  set inbufs ${inst}/u_core/u_targ_inbufs
  set cdc_max [expr {$clk_period * $::i3c_cfg(cdc_fraction)}]

  # The Target input buffers gate the bus clocks with a plain AND/OR
  # (i3c_clock_buf_en.sv) rather than an integrated clock gate, and select
  # the scan clock through a mux. The enable only changes while the bus is
  # idle (i3c_target_rst.sv), so the gating check is not meaningful.
  foreach buf {u_scl_buf u_scl_inv u_sda0_clk u_sda0_clk_n} {
    if {[i3c_has_command set_disable_clock_gating_check]} {
      i3c_try "clock gating check on ${buf}" {
        set cells [get_cells -quiet ${inbufs}/${buf}/*]
        if {[llength $cells]} {
          set_disable_clock_gating_check $cells
        }
      }
    }
    # Never take the scan branch of the clock mux in functional analysis, so
    # the scan clock does not appear on the bus clock trees.
    i3c_case_if_present 0 ${inbufs}/${buf}/u_mux/sel_i
  }
  # Keep the quasi-static buffer enable out of timing.
  i3c_try "target buffer enable" {
    set en_q [i3c_pins ${inst}/u_core/u_targ_rst/*buf_en_q*/Q OUT]
    if {[llength $en_q]} {
      set_false_path -from $en_q
    }
  }

  # Bus clocks to and from clk_i. Every crossing uses either prim_flop_2sync or
  # the toggle handshake in i3c_sync_data, so bounding the data path is enough.
  foreach sync {
    u_core/u_sync_ctrl
    u_core/u_sync_targ
    u_core/u_reg_sync
    u_core/u_target/u_in_sync
    u_core/u_target/u_edge_det
    u_core/u_target/u_trx_rxd_sync
    u_core/u_target/u_targ_txc_sync
    u_core/u_target/u_arb_sync
    u_core/u_target/gen_targ_txd_sync[*].u_targ_txd_sync
  } {
    i3c_try "CDC bound on ${sync}" {
      set endpoints [i3c_pins ${inst}/${sync}/*u_sync_1*/D IN]
      if {[llength $endpoints]} {
        set_max_delay $cdc_max -to $endpoints
      }
    }
  }
  # i3c_sync_data carries its payload combinationally alongside the toggle, so
  # the data has to be bounded too (i3c_sync_data.sv).
  i3c_try "CDC bound on i3c_sync_data payloads" {
    set sync_data [i3c_pins ${inst}/u_core/u_target/*sync*/dst_data_q_reg*/D IN]
    if {[llength $sync_data]} {
      set_max_delay $cdc_max -to $sync_data
    }
  }

  # The Target transceiver's reset is released by a clk_i flop into the
  # SCL/SDA domains (i3c_core.sv).
  i3c_try "transceiver reset bound" {
    set rst_src [i3c_pins ${inst}/u_core/u_targ_rst_src/*/Q OUT]
    if {[llength $rst_src]} {
      set_max_delay $cdc_max -from $rst_src
    }
  }

  # Quasi-static device address and group address configuration, written while
  # the Target is disabled (i3c_target_trx.sv, TODO #31065).
  foreach cfg_pin {targ_dev_i grp_addr_i addr_blocked_i mask_blocked_i} {
    i3c_try "quasi-static ${cfg_pin}" {
      # These are hierarchical pins on the transceiver boundary, which are not
      # valid endpoints, so bound whatever passes through them instead.
      set pins [get_pins -quiet ${inst}/u_core/u_targ_trx/${cfg_pin}*]
      if {[llength $pins]} {
        set_max_delay $cdc_max -through $pins
      }
    }
  }

  # SDA is buffered as data while SCL is buffered as a clock; the two have to
  # stay close enough for the Target to sample SDA correctly
  # (i3c_input_buffers.sv, TODO #31335).
  i3c_try "SCL/SDA skew" {
    set sda_data [i3c_pins ${inbufs}/u_sda_buf/*/out_o* OUT]
    if {[llength $sda_data]} {
      set_max_delay $::i3c_cfg(sda_skew_max) -from $sda_data
    }
  }

  # SCL leaves the Controller as the OR of a posedge and a negedge flop. The
  # bus is unusable if that OR glitches, so keep the two contributions close
  # (integration_notes.md:51).
  i3c_try "SCL output skew" {
    set scl_flops [i3c_pins ${inst}/u_core/u_ctrl_trx/*scl_n*/Q OUT]
    set scl_out [get_pins -quiet ${inst}/cio_scl_o]
    if {[llength $scl_flops] && [llength $scl_out]} {
      set_max_delay $::i3c_cfg(scl_out_skew_max) -from $scl_flops -to $scl_out
    }
  }

  # The START/STOP detectors are clocked by SDA and take SCL as their data
  # (i3c_target_trx.sv). SDA and SCL are separate asynchronous clocks,
  # so this clock-as-data path has to be bounded explicitly. The specification
  # allows tCAS after a START before the first SCL edge, and tCBP before a
  # STOP, which is the window the detectors have to resolve in.
  foreach det {stop_det start_det rep_start_det rep_start_pre} {
    i3c_try "START/STOP detector ${det}" {
      set det_d [i3c_pins ${inst}/u_core/u_targ_trx/*${det}*/D IN]
      if {[llength $det_d]} {
        set_max_delay $::i3c_cfg(start_stop_max) -to $det_d
      }
    }
  }
}

#############################
# Entry point               #
#############################

# Constrain one I3C instance end to end.
proc i3c_constrain {inst scl_port sda_port prefix clk_pin clk_name clk_period} {
  i3c_create_clocks $inst $scl_port $sda_port $prefix $clk_pin $clk_name
  i3c_set_io_delays $inst $scl_port $sda_port $prefix $clk_name
  i3c_set_internal_paths $inst $clk_name $clk_period
}
