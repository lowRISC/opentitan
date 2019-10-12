// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import tl_agent_pkg::*;
  import chip_env_pkg::*;
  import top_pkg::*;
  import chip_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"
  `include "chip_hier_macros.svh"

  wire clk, rst_n;
  wire [NUM_GPIOS-1:0] gpio_pins;
  wire jtag_tck;
  wire jtag_tms;
  wire jtag_trst_n;
  wire jtag_tdi;
  wire jtag_tdo;

  bit stub_cpu;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  pins_if #(NUM_GPIOS) gpio_if(.pins(gpio_pins));
  tl_if   cpu_d_tl_if(.clk(clk), .rst_n(rst_n));
  uart_if uart_if();
  jtag_if jtag_if();

  // backdoors
  bind `ROM_HIER mem_bkdr_if rom_mem_bkdr_if();
  bind `FLASH0_MEM_HIER mem_bkdr_if flash0_mem_bkdr_if();
  bind `FLASH1_MEM_HIER mem_bkdr_if flash1_mem_bkdr_if();

  top_earlgrey_asic dut (
    // Clock and Reset
    .IO_CLK     (clk),
    .IO_RST_N   (rst_n),
    // JTAG interface
    .IO_JTCK    (jtag_tck),
    .IO_JTMS    (jtag_tms),
    .IO_JTRST_N (jtag_trst_n),
    .IO_JTDI    (jtag_tdi),
    .IO_JTDO    (jtag_tdo),
    // UART interface
    .IO_URX     (uart_if.uart_rx),
    .IO_UTX     (uart_if.uart_tx),
    // GPIO x 16 interface
    .IO_GP0     (gpio_pins[0 ]),
    .IO_GP1     (gpio_pins[1 ]),
    .IO_GP2     (gpio_pins[2 ]),
    .IO_GP3     (gpio_pins[3 ]),
    .IO_GP4     (gpio_pins[4 ]),
    .IO_GP5     (gpio_pins[5 ]),
    .IO_GP6     (gpio_pins[6 ]),
    .IO_GP7     (gpio_pins[7 ]),
    .IO_GP8     (gpio_pins[8 ]),
    .IO_GP9     (gpio_pins[9 ]),
    .IO_GP10    (gpio_pins[10]),
    .IO_GP11    (gpio_pins[11]),
    .IO_GP12    (gpio_pins[12]),
    .IO_GP13    (gpio_pins[13]),
    .IO_GP14    (gpio_pins[14]),
    .IO_GP15    (gpio_pins[15])
  );

  // connect sw_msg_monitor
  bit                 sw_msg_monitor_valid;
  bit [TL_AW-1:0]     sw_msg_monitor_sw_msg_addr;

  sw_msg_monitor_if sw_msg_monitor_if (
    .clk              (`RAM_MAIN_HIER.clk_i),
    .rst_n            (`RAM_MAIN_HIER.rst_ni),
    .valid            (sw_msg_monitor_valid),
    .addr_data        (`RAM_MAIN_HIER.wdata_i),
    .sw_msg_addr      (sw_msg_monitor_sw_msg_addr)
  );
  assign sw_msg_monitor_valid = `RAM_MAIN_HIER.req_i && `RAM_MAIN_HIER.write_i &&
                                (`RAM_MAIN_HIER.addr_i == sw_msg_monitor_sw_msg_addr);

  // connect signals
  assign jtag_tck         = jtag_if.tck;
  assign jtag_tms         = jtag_if.tms;
  assign jtag_trst_n      = jtag_if.trst_n;
  assign jtag_tdi         = jtag_if.tdi;
  assign jtag_if.tdo      = jtag_tdo;
  assign cpu_d_tl_if.d2h  = `CPU_HIER.tl_d_i;

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_cpu_d_tl_agent*", "vif", cpu_d_tl_if);
    uvm_config_db#(virtual pins_if #(NUM_GPIOS))::set(null, "*.env", "gpio_vif", gpio_if);
    uvm_config_db#(virtual uart_if)::set(null, "*.env.m_uart_agent*", "vif", uart_if);
    uvm_config_db#(virtual jtag_if)::set(null, "*.env.m_jtag_agent*", "vif", jtag_if);
    uvm_config_db#(virtual mem_bkdr_if)::set(null, "*.env", "mem_bkdr_vifs[Rom]",
        `ROM_HIER.rom_mem_bkdr_if);
    uvm_config_db#(virtual mem_bkdr_if)::set(null, "*.env", "mem_bkdr_vifs[FlashBank0]",
        `FLASH0_MEM_HIER.flash0_mem_bkdr_if);
    uvm_config_db#(virtual mem_bkdr_if)::set(null, "*.env", "mem_bkdr_vifs[FlashBank1]",
        `FLASH1_MEM_HIER.flash1_mem_bkdr_if);
    uvm_config_db#(virtual sw_msg_monitor_if)::set(null, "*.env", "sw_msg_monitor_vif",
        sw_msg_monitor_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

  // stub cpu environment
  // if enabled, clock to cpu is forced to 0
  // cpu_d_tl_if force are applied to cpu d tl interface
  initial begin
    void'($value$plusargs("stub_cpu=%0b", stub_cpu));
    if (stub_cpu) begin
      force `CPU_HIER.clk_i = 1'b0;
      force `CPU_HIER.tl_d_o = cpu_d_tl_if.h2d;
    end
    else begin
      force cpu_d_tl_if.h2d = `CPU_HIER.tl_d_o;
    end
  end

endmodule
