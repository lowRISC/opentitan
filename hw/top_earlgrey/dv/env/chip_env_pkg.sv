// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package chip_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import flash_ctrl_pkg::*;
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
  `include "autogen/alert_handler_env_pkg__params.sv"

  // local parameters and types
  parameter uint NUM_GPIOS = 16;
  parameter uint NUM_UART_INST = 4;
  // Buffer is half of SPI_DEVICE Dual Port SRAM
  parameter uint SPI_FRAME_BYTE_SIZE = spi_device_reg_pkg::SPI_DEVICE_BUFFER_SIZE/2;

  // SW constants - use unmapped address space with at least 32 bytes.
  parameter bit [TL_AW-1:0] SW_DV_START_ADDR        = 32'h3000_0000;
  parameter bit [TL_AW-1:0] SW_DV_TEST_STATUS_ADDR  = SW_DV_START_ADDR + 0;
  parameter bit [TL_AW-1:0] SW_DV_LOG_ADDR          = SW_DV_START_ADDR + 4;

  typedef virtual pins_if #(NUM_GPIOS)  gpio_vif;
  typedef virtual mem_bkdr_if           mem_bkdr_vif;
  typedef virtual sw_logger_if          sw_logger_vif;
  typedef virtual sw_test_status_if     sw_test_status_vif;

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

  // On OpenTitan, we deal with 3 types of SW - ROM, the main test and OTBN. This basically puts
  // these SW types into 'slots' that the external regression tool can set.
  typedef enum {
    SwTypeRom,  // Ibex SW - first stage boot ROM.
    SwTypeTest, // Ibex SW - actual test SW.
    SwTypeOtbn  // Otbn SW.
  } sw_type_e;

  // TODO, better to generate this enum
  typedef enum {
    kTopEarlgreyPlicIrqIdNone = 0,
    kTopEarlgreyPlicIrqIdUart0TxWatermark = 1,
    kTopEarlgreyPlicIrqIdUart0RxWatermark = 2,
    kTopEarlgreyPlicIrqIdUart0TxEmpty = 3,
    kTopEarlgreyPlicIrqIdUart0RxOverflow = 4,
    kTopEarlgreyPlicIrqIdUart0RxFrameErr = 5,
    kTopEarlgreyPlicIrqIdUart0RxBreakErr = 6,
    kTopEarlgreyPlicIrqIdUart0RxTimeout = 7,
    kTopEarlgreyPlicIrqIdUart0RxParityErr = 8,
    kTopEarlgreyPlicIrqIdUart1TxWatermark = 9,
    kTopEarlgreyPlicIrqIdUart1RxWatermark = 10,
    kTopEarlgreyPlicIrqIdUart1TxEmpty = 11,
    kTopEarlgreyPlicIrqIdUart1RxOverflow = 12,
    kTopEarlgreyPlicIrqIdUart1RxFrameErr = 13,
    kTopEarlgreyPlicIrqIdUart1RxBreakErr = 14,
    kTopEarlgreyPlicIrqIdUart1RxTimeout = 15,
    kTopEarlgreyPlicIrqIdUart1RxParityErr = 16,
    kTopEarlgreyPlicIrqIdUart2TxWatermark = 17,
    kTopEarlgreyPlicIrqIdUart2RxWatermark = 18,
    kTopEarlgreyPlicIrqIdUart2TxEmpty = 19,
    kTopEarlgreyPlicIrqIdUart2RxOverflow = 20,
    kTopEarlgreyPlicIrqIdUart2RxFrameErr = 21,
    kTopEarlgreyPlicIrqIdUart2RxBreakErr = 22,
    kTopEarlgreyPlicIrqIdUart2RxTimeout = 23,
    kTopEarlgreyPlicIrqIdUart2RxParityErr = 24,
    kTopEarlgreyPlicIrqIdUart3TxWatermark = 25,
    kTopEarlgreyPlicIrqIdUart3RxWatermark = 26,
    kTopEarlgreyPlicIrqIdUart3TxEmpty = 27,
    kTopEarlgreyPlicIrqIdUart3RxOverflow = 28,
    kTopEarlgreyPlicIrqIdUart3RxFrameErr = 29,
    kTopEarlgreyPlicIrqIdUart3RxBreakErr = 30,
    kTopEarlgreyPlicIrqIdUart3RxTimeout = 31,
    kTopEarlgreyPlicIrqIdUart3RxParityErr = 32,
    kTopEarlgreyPlicIrqIdGpioGpio0 = 33,
    kTopEarlgreyPlicIrqIdGpioGpio1 = 34,
    kTopEarlgreyPlicIrqIdGpioGpio2 = 35,
    kTopEarlgreyPlicIrqIdGpioGpio3 = 36,
    kTopEarlgreyPlicIrqIdGpioGpio4 = 37,
    kTopEarlgreyPlicIrqIdGpioGpio5 = 38,
    kTopEarlgreyPlicIrqIdGpioGpio6 = 39,
    kTopEarlgreyPlicIrqIdGpioGpio7 = 40,
    kTopEarlgreyPlicIrqIdGpioGpio8 = 41,
    kTopEarlgreyPlicIrqIdGpioGpio9 = 42,
    kTopEarlgreyPlicIrqIdGpioGpio10 = 43,
    kTopEarlgreyPlicIrqIdGpioGpio11 = 44,
    kTopEarlgreyPlicIrqIdGpioGpio12 = 45,
    kTopEarlgreyPlicIrqIdGpioGpio13 = 46,
    kTopEarlgreyPlicIrqIdGpioGpio14 = 47,
    kTopEarlgreyPlicIrqIdGpioGpio15 = 48,
    kTopEarlgreyPlicIrqIdGpioGpio16 = 49,
    kTopEarlgreyPlicIrqIdGpioGpio17 = 50,
    kTopEarlgreyPlicIrqIdGpioGpio18 = 51,
    kTopEarlgreyPlicIrqIdGpioGpio19 = 52,
    kTopEarlgreyPlicIrqIdGpioGpio20 = 53,
    kTopEarlgreyPlicIrqIdGpioGpio21 = 54,
    kTopEarlgreyPlicIrqIdGpioGpio22 = 55,
    kTopEarlgreyPlicIrqIdGpioGpio23 = 56,
    kTopEarlgreyPlicIrqIdGpioGpio24 = 57,
    kTopEarlgreyPlicIrqIdGpioGpio25 = 58,
    kTopEarlgreyPlicIrqIdGpioGpio26 = 59,
    kTopEarlgreyPlicIrqIdGpioGpio27 = 60,
    kTopEarlgreyPlicIrqIdGpioGpio28 = 61,
    kTopEarlgreyPlicIrqIdGpioGpio29 = 62,
    kTopEarlgreyPlicIrqIdGpioGpio30 = 63,
    kTopEarlgreyPlicIrqIdGpioGpio31 = 64,
    kTopEarlgreyPlicIrqIdSpiDeviceRxf = 65,
    kTopEarlgreyPlicIrqIdSpiDeviceRxlvl = 66,
    kTopEarlgreyPlicIrqIdSpiDeviceTxlvl = 67,
    kTopEarlgreyPlicIrqIdSpiDeviceRxerr = 68,
    kTopEarlgreyPlicIrqIdSpiDeviceRxoverflow = 69,
    kTopEarlgreyPlicIrqIdSpiDeviceTxunderflow = 70,
    kTopEarlgreyPlicIrqIdI2c0FmtWatermark = 71,
    kTopEarlgreyPlicIrqIdI2c0RxWatermark = 72,
    kTopEarlgreyPlicIrqIdI2c0FmtOverflow = 73,
    kTopEarlgreyPlicIrqIdI2c0RxOverflow = 74,
    kTopEarlgreyPlicIrqIdI2c0Nak = 75,
    kTopEarlgreyPlicIrqIdI2c0SclInterference = 76,
    kTopEarlgreyPlicIrqIdI2c0SdaInterference = 77,
    kTopEarlgreyPlicIrqIdI2c0StretchTimeout = 78,
    kTopEarlgreyPlicIrqIdI2c0SdaUnstable = 79,
    kTopEarlgreyPlicIrqIdI2c0TransComplete = 80,
    kTopEarlgreyPlicIrqIdI2c0TxEmpty = 81,
    kTopEarlgreyPlicIrqIdI2c0TxNonempty = 82,
    kTopEarlgreyPlicIrqIdI2c0TxOverflow = 83,
    kTopEarlgreyPlicIrqIdI2c0AcqOverflow = 84,
    kTopEarlgreyPlicIrqIdI2c0AckStop = 85,
    kTopEarlgreyPlicIrqIdI2c0HostTimeout = 86,
    kTopEarlgreyPlicIrqIdI2c1FmtWatermark = 87,
    kTopEarlgreyPlicIrqIdI2c1RxWatermark = 88,
    kTopEarlgreyPlicIrqIdI2c1FmtOverflow = 89,
    kTopEarlgreyPlicIrqIdI2c1RxOverflow = 90,
    kTopEarlgreyPlicIrqIdI2c1Nak = 91,
    kTopEarlgreyPlicIrqIdI2c1SclInterference = 92,
    kTopEarlgreyPlicIrqIdI2c1SdaInterference = 93,
    kTopEarlgreyPlicIrqIdI2c1StretchTimeout = 94,
    kTopEarlgreyPlicIrqIdI2c1SdaUnstable = 95,
    kTopEarlgreyPlicIrqIdI2c1TransComplete = 96,
    kTopEarlgreyPlicIrqIdI2c1TxEmpty = 97,
    kTopEarlgreyPlicIrqIdI2c1TxNonempty = 98,
    kTopEarlgreyPlicIrqIdI2c1TxOverflow = 99,
    kTopEarlgreyPlicIrqIdI2c1AcqOverflow = 100,
    kTopEarlgreyPlicIrqIdI2c1AckStop = 101,
    kTopEarlgreyPlicIrqIdI2c1HostTimeout = 102,
    kTopEarlgreyPlicIrqIdI2c2FmtWatermark = 103,
    kTopEarlgreyPlicIrqIdI2c2RxWatermark = 104,
    kTopEarlgreyPlicIrqIdI2c2FmtOverflow = 105,
    kTopEarlgreyPlicIrqIdI2c2RxOverflow = 106,
    kTopEarlgreyPlicIrqIdI2c2Nak = 107,
    kTopEarlgreyPlicIrqIdI2c2SclInterference = 108,
    kTopEarlgreyPlicIrqIdI2c2SdaInterference = 109,
    kTopEarlgreyPlicIrqIdI2c2StretchTimeout = 110,
    kTopEarlgreyPlicIrqIdI2c2SdaUnstable = 111,
    kTopEarlgreyPlicIrqIdI2c2TransComplete = 112,
    kTopEarlgreyPlicIrqIdI2c2TxEmpty = 113,
    kTopEarlgreyPlicIrqIdI2c2TxNonempty = 114,
    kTopEarlgreyPlicIrqIdI2c2TxOverflow = 115,
    kTopEarlgreyPlicIrqIdI2c2AcqOverflow = 116,
    kTopEarlgreyPlicIrqIdI2c2AckStop = 117,
    kTopEarlgreyPlicIrqIdI2c2HostTimeout = 118,
    kTopEarlgreyPlicIrqIdPattgenDoneCh0 = 119,
    kTopEarlgreyPlicIrqIdPattgenDoneCh1 = 120,
    kTopEarlgreyPlicIrqIdFlashCtrlProgEmpty = 121,
    kTopEarlgreyPlicIrqIdFlashCtrlProgLvl = 122,
    kTopEarlgreyPlicIrqIdFlashCtrlRdFull = 123,
    kTopEarlgreyPlicIrqIdFlashCtrlRdLvl = 124,
    kTopEarlgreyPlicIrqIdFlashCtrlOpDone = 125,
    kTopEarlgreyPlicIrqIdHmacHmacDone = 126,
    kTopEarlgreyPlicIrqIdHmacFifoEmpty = 127,
    kTopEarlgreyPlicIrqIdHmacHmacErr = 128,
    kTopEarlgreyPlicIrqIdAlertHandlerClassa = 129,
    kTopEarlgreyPlicIrqIdAlertHandlerClassb = 130,
    kTopEarlgreyPlicIrqIdAlertHandlerClassc = 131,
    kTopEarlgreyPlicIrqIdAlertHandlerClassd = 132,
    kTopEarlgreyPlicIrqIdUsbdevPktReceived = 133,
    kTopEarlgreyPlicIrqIdUsbdevPktSent = 134,
    kTopEarlgreyPlicIrqIdUsbdevDisconnected = 135,
    kTopEarlgreyPlicIrqIdUsbdevHostLost = 136,
    kTopEarlgreyPlicIrqIdUsbdevLinkReset = 137,
    kTopEarlgreyPlicIrqIdUsbdevLinkSuspend = 138,
    kTopEarlgreyPlicIrqIdUsbdevLinkResume = 139,
    kTopEarlgreyPlicIrqIdUsbdevAvEmpty = 140,
    kTopEarlgreyPlicIrqIdUsbdevRxFull = 141,
    kTopEarlgreyPlicIrqIdUsbdevAvOverflow = 142,
    kTopEarlgreyPlicIrqIdUsbdevLinkInErr = 143,
    kTopEarlgreyPlicIrqIdUsbdevRxCrcErr = 144,
    kTopEarlgreyPlicIrqIdUsbdevRxPidErr = 145,
    kTopEarlgreyPlicIrqIdUsbdevRxBitstuffErr = 146,
    kTopEarlgreyPlicIrqIdUsbdevFrame = 147,
    kTopEarlgreyPlicIrqIdUsbdevConnected = 148,
    kTopEarlgreyPlicIrqIdUsbdevLinkOutErr = 149,
    kTopEarlgreyPlicIrqIdPwrmgrAonWakeup = 150,
    kTopEarlgreyPlicIrqIdOtbnDone = 151,
    kTopEarlgreyPlicIrqIdKeymgrOpDone = 152,
    kTopEarlgreyPlicIrqIdKmacKmacDone = 153,
    kTopEarlgreyPlicIrqIdKmacFifoEmpty = 154,
    kTopEarlgreyPlicIrqIdKmacKmacErr = 155,
    kTopEarlgreyPlicIrqIdOtpCtrlOtpOperationDone = 156,
    kTopEarlgreyPlicIrqIdOtpCtrlOtpError = 157,
    kTopEarlgreyPlicIrqIdCsrngCsCmdReqDone = 158,
    kTopEarlgreyPlicIrqIdCsrngCsEntropyReq = 159,
    kTopEarlgreyPlicIrqIdCsrngCsHwInstExc = 160,
    kTopEarlgreyPlicIrqIdCsrngCsFatalErr = 161,
    kTopEarlgreyPlicIrqIdEdn0EdnCmdReqDone = 162,
    kTopEarlgreyPlicIrqIdEdn0EdnFatalErr = 163,
    kTopEarlgreyPlicIrqIdEdn1EdnCmdReqDone = 164,
    kTopEarlgreyPlicIrqIdEdn1EdnFatalErr = 165,
    kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired = 166,
    kTopEarlgreyPlicIrqIdAonTimerAonWdogTimerBark = 167,
    kTopEarlgreyPlicIrqIdEntropySrcEsEntropyValid = 168,
    kTopEarlgreyPlicIrqIdEntropySrcEsHealthTestFailed = 169,
    kTopEarlgreyPlicIrqIdEntropySrcEsFatalErr = 170
  } top_earlgrey_plic_irq_id_e;

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

  function automatic chip_mem_e get_chip_mem_by_addr(bit [bus_params_pkg::BUS_AW-1:0] addr);
    if (addr inside {[top_earlgrey_pkg::TOP_EARLGREY_ROM_BASE_ADDR :
                      top_earlgrey_pkg::TOP_EARLGREY_ROM_BASE_ADDR +
                      top_earlgrey_pkg::TOP_EARLGREY_ROM_SIZE_BYTES - 1]}) begin
      return Rom;
    end else if (addr inside {[top_earlgrey_pkg::TOP_EARLGREY_RAM_MAIN_BASE_ADDR :
                      top_earlgrey_pkg::TOP_EARLGREY_RAM_MAIN_BASE_ADDR +
                      top_earlgrey_pkg::TOP_EARLGREY_RAM_MAIN_SIZE_BYTES - 1]}) begin
      return RamMain;
    end else if (addr inside {[top_earlgrey_pkg::TOP_EARLGREY_RAM_RET_AON_BASE_ADDR :
                      top_earlgrey_pkg::TOP_EARLGREY_RAM_RET_AON_BASE_ADDR +
                      top_earlgrey_pkg::TOP_EARLGREY_RAM_RET_AON_SIZE_BYTES - 1]}) begin
      return RamRet;
    end else if (addr inside {[top_earlgrey_pkg::TOP_EARLGREY_EFLASH_BASE_ADDR :
                      top_earlgrey_pkg::TOP_EARLGREY_EFLASH_BASE_ADDR +
                      top_earlgrey_pkg::TOP_EARLGREY_EFLASH_SIZE_BYTES / 2 - 1]}) begin
      return FlashBank0;
    end else if (addr inside {[top_earlgrey_pkg::TOP_EARLGREY_EFLASH_BASE_ADDR +
                      top_earlgrey_pkg::TOP_EARLGREY_EFLASH_SIZE_BYTES / 2 :
                      top_earlgrey_pkg::TOP_EARLGREY_EFLASH_BASE_ADDR +
                      top_earlgrey_pkg::TOP_EARLGREY_EFLASH_SIZE_BYTES - 1]}) begin
      return FlashBank1;
    end else if (addr inside {[top_earlgrey_pkg::TOP_EARLGREY_SPI_DEVICE_BASE_ADDR :
                      top_earlgrey_pkg::TOP_EARLGREY_SPI_DEVICE_BASE_ADDR +
                      top_earlgrey_pkg::TOP_EARLGREY_SPI_DEVICE_SIZE_BYTES - 1]}) begin
      return SpiMem;
   end else begin
     `uvm_fatal("chip_env_pkg", $sformatf("Invalid mem addr: 0x%0h", addr))
   end
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
