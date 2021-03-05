// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package chip_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import flash_ctrl_pkg::*;
  import otp_ctrl_pkg::*;
  import sram_ctrl_pkg::*;
  import dv_utils_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import tl_agent_pkg::*;
  import uart_agent_pkg::*;
  import jtag_agent_pkg::*;
  import spi_agent_pkg::*;
  import dv_lib_pkg::*;
  import cip_base_pkg::*;
  import chip_ral_pkg::*;
  import sw_test_status_pkg::*;
  import xbar_env_pkg::*;
  import bus_params_pkg::*;
  import str_utils_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // include auto-generated alert related parameters
  `include "autogen/chip_env_pkg__params.sv"

  // local parameters and types
  parameter uint NUM_GPIOS = 16;
  // Buffer is half of SPI_DEVICE Dual Port SRAM
  parameter uint SPI_FRAME_BYTE_SIZE = spi_device_reg_pkg::SPI_DEVICE_BUFFER_SIZE/2;

  // SW constants - use unmapped address space with at least 32 bytes.
  parameter bit [TL_AW-1:0] SW_DV_START_ADDR        = 32'h3000_0000;
  parameter bit [TL_AW-1:0] SW_DV_TEST_STATUS_ADDR  = SW_DV_START_ADDR + 0;
  parameter bit [TL_AW-1:0] SW_DV_LOG_ADDR          = SW_DV_START_ADDR + 4;

  typedef virtual pins_if #(NUM_GPIOS)  gpio_vif;
  typedef virtual sw_logger_if          sw_logger_vif;
  typedef virtual sw_test_status_if     sw_test_status_vif;

  // backdoors
  typedef virtual mem_bkdr_if mem_bkdr_vif;
  typedef virtual mem_bkdr_if #(.MEM_PARITY(1)) parity_mem_bkdr_vif;
  typedef virtual mem_bkdr_if #(.MEM_ECC(1)) ecc_mem_bkdr_vif;

  // Types of memories in the chip.
  typedef enum {
    Rom,
    RamMain,
    RamRet,
    FlashBank0,
    FlashBank1,
    FlashBank0Info,
    FlashBank1Info,
    Otp,
    SpiMem
  } chip_mem_e;

  // On OpenTitan, we deal with 4 types of SW - ROM, the main test, the OTBN test and the OTP image.
  // This basically puts these SW types into 'slots' that the external regression tool can set.
  typedef enum {
    SwTypeRom,  // Ibex SW - first stage boot ROM.
    SwTypeTest, // Ibex SW - actual test SW.
    SwTypeOtbn, // Otbn SW.
    SwTypeOtp   // OTP image.
  } sw_type_e;

  // functions
  function automatic bit [bus_params_pkg::BUS_AW-1:0] get_chip_mem_base_addr(chip_mem_e mem);
    case (mem)
      Rom:    return top_earlgrey_pkg::TOP_EARLGREY_ROM_BASE_ADDR;
      RamMain:return top_earlgrey_pkg::TOP_EARLGREY_RAM_MAIN_BASE_ADDR;
      RamRet: return top_earlgrey_pkg::TOP_EARLGREY_RAM_RET_AON_BASE_ADDR;
      FlashBank0, FlashBank0Info: return top_earlgrey_pkg::TOP_EARLGREY_EFLASH_BASE_ADDR;
      FlashBank1, FlashBank1Info: return top_earlgrey_pkg::TOP_EARLGREY_EFLASH_BASE_ADDR +
                                         flash_ctrl_pkg::PagesPerBank *
                                         flash_ctrl_pkg::WordsPerPage *
                                         flash_ctrl_pkg::DataWidth / 8;
      SpiMem: return top_earlgrey_pkg::TOP_EARLGREY_SPI_DEVICE_BASE_ADDR
                      + spi_device_reg_pkg::SPI_DEVICE_BUFFER_OFFSET ; // TODO
      default:`uvm_fatal("chip_env_pkg", {"Invalid input: ", mem.name()})
    endcase
  endfunction

  // Extracts the address and size of a const symbol in a SW test (supplied as an ELF file).
  //
  // Used by a testbench to modify the given symbol in an executable (elf) generated for an embedded
  // CPU within the DUT. This function only returns the extracted address and size of the symbol
  // using the readelf utility. Readelf comes with binutils, a package typically available on user
  // / corp machines. If not available, the assumption is, it can be relatively easily installed.
  // The actual job of writing the new value into the symbol is handled externally (often via a
  // backdoor mechanism to write the memory).
  function automatic void sw_symbol_get_addr_size(input string elf_file,
                                                  input string symbol,
                                                  output longint unsigned addr,
                                                  output longint unsigned size);

    string msg_id = "sw_symbol_get_addr_size";
    `DV_CHECK_STRNE_FATAL(elf_file, "", "Input arg \"elf_file\" cannot be an empty string", msg_id)
    `DV_CHECK_STRNE_FATAL(symbol,   "", "Input arg \"symbol\" cannot be an empty string", msg_id)

    begin
      int ret;
      string line;
      int out_file_d = 0;
      string out_file = $sformatf("%0s.dat", symbol);
      string cmd = $sformatf(
          // use `--wide` to avoid truncating the output, in case of long symbol name
          "/usr/bin/readelf -s --wide %0s | grep %0s | awk \'{print $2\" \"$3}\' > %0s",
          elf_file, symbol, out_file);

      // TODO #3838: shell pipes are bad 'mkay?
      ret = $system(cmd);
      `DV_CHECK_EQ_FATAL(ret, 0, $sformatf("Command \"%0s\" failed with exit code %0d", cmd, ret),
                         msg_id)

      out_file_d = $fopen(out_file, "r");
      `DV_CHECK_FATAL(out_file_d, $sformatf("Failed to open \"%0s\"", out_file), msg_id)

      ret = $fgets(line, out_file_d);
      `DV_CHECK_FATAL(ret, $sformatf("Failed to read line from \"%0s\"", out_file), msg_id)

      // The first line should have the addr in hex followed by its size as integer.
      ret = $sscanf(line, "%h %d", addr, size);
      `DV_CHECK_EQ_FATAL(ret, 2, $sformatf("Failed to extract {addr size} from line \"%0s\"", line),
                         msg_id)

      // Attempt to read the next line should be met with EOF.
      void'($fgets(line, out_file_d));
      ret = $feof(out_file_d);
      `DV_CHECK_FATAL(ret, $sformatf("EOF expected to be reached for \"%0s\"", out_file), msg_id)
      $fclose(out_file_d);

      ret = $system($sformatf("rm -rf %0s", out_file));
      `DV_CHECK_EQ_FATAL(ret, 0, $sformatf("Failed to delete \"%0s\"", out_file), msg_id)
    end
  endfunction

  // package sources
  `include "chip_env_cfg.sv"
  `include "chip_env_cov.sv"
  `include "chip_virtual_sequencer.sv"
  `include "chip_scoreboard.sv"
  `include "chip_env.sv"
  `include "chip_vseq_list.sv"

endpackage
