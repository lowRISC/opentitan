onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/clk_i
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/rst_ni
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/reg2hw
add wave -noupdate -childformat {{/testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/hw2reg.event_clk_counter3_reg -radix unsigned} {/testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/hw2reg.event_clk_counter2_reg -radix unsigned} {/testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/hw2reg.event_clk_counter1_reg -radix unsigned} {/testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/hw2reg.event_clk_counter0_reg -radix unsigned}} -subitemconfig {/testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/hw2reg.event_clk_counter3_reg {-height 17 -radix unsigned} /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/hw2reg.event_clk_counter2_reg {-height 17 -radix unsigned} /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/hw2reg.event_clk_counter1_reg {-height 17 -radix unsigned} /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/hw2reg.event_clk_counter0_reg {-height 17 -radix unsigned -expand}} /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/hw2reg
add wave -noupdate -expand /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/events
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/events_counters_mux
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/event_clk_counters_rst
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/events_counters_mux_reg_events_counter0_mux_qs
add wave -noupdate -divider {EVENT COUNTERS}
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/event_counters_rst
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/events_counters_mux_reg_events_counter3_mux_qs
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/events_counters_mux_reg_events_counter2_mux_qs
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/events_counters_mux_reg_events_counter1_mux_qs
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/events_counters_mux_reg_events_counter0_mux_qs
add wave -noupdate -radix unsigned /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/event_counter3_reg
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/event_counter3_en
add wave -noupdate -radix unsigned /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/event_counter2_reg
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/event_counter2_en
add wave -noupdate -radix unsigned /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/event_counter1_reg
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/event_counter1_en
add wave -noupdate -radix unsigned /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/event_counter0_reg
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/event_counter0_en
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/reg2hw
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/reg2hw.events_counters_mux_reg.events_counter3_mux.q
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/reg2hw
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/reg2hw.events_counters_mux_reg.events_counter2_mux.q
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/reg2hw
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/reg2hw.events_counters_mux_reg.events_counter1_mux.q
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/reg2hw
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/reg2hw.events_counters_mux_reg.events_counter0_mux.q
add wave -noupdate -divider {EVENT CLK COUNTERS}
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/event_clk_counter3_reg
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/event_clk_counter3_en
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/event_clk_counter2_reg
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/event_clk_counter2_en
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/event_clk_counter1_reg
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/event_clk_counter1_en
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/event_clk_counter0_reg
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/event_clk_counter0_en
add wave -noupdate -expand /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_core/perfcounters_t_event/event_clk_counters_rst
add wave -noupdate -divider {REG IF}
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/hw2reg
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/intg_err
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/intg_err_o
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/reg2hw
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/reg_we
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/reg_re
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/reg_addr
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/reg_wdata
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/reg_rdata
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/reg_be
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/reg_busy
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/reg_error
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/reg_rdata_next
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/reg_we_check
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/reg_we_err
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/rst_ni
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/shadow_busy
add wave -noupdate -expand /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/tl_i
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/tl_o
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/tl_o_pre
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/tl_reg_d2h
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/tl_reg_h2d
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/unused_be
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/unused_wdata
add wave -noupdate /testbench_asynch_astral/dut/u_RoT/perfcounters_t/perfcounters_t_reg_top/wr_err
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {1218305000 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 779
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 0
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ps
update
WaveRestoreZoom {0 ps} {2179138500 ps}
