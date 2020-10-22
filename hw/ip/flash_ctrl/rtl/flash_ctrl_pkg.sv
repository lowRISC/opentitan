// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash Controller module.
//

package flash_ctrl_pkg;

  // design constants
  parameter int DataWidth       = top_pkg::FLASH_DATA_WIDTH;
  parameter int NumBanks        = top_pkg::FLASH_BANKS;
  parameter int InfoTypes       = top_pkg::FLASH_INFO_TYPES; // How many types of info per bank

// TBD, the following hard-wired values are there to work-around verilator.
// For some reason if the values are assigned through parameters verilator thinks
// they are not constant
`ifdef VERILATOR
  parameter int InfoTypeSize [InfoTypes] = '{4, 4}; // size per bank
  parameter int InfosPerBank    = max_info_pages('{4, 4});
`else
  parameter int InfoTypeSize [InfoTypes] = top_pkg::FLASH_INFO_PER_BANK; // size per bank
  parameter int InfosPerBank    = max_info_pages(InfoTypeSize);
`endif
  parameter int PagesPerBank    = top_pkg::FLASH_PAGES_PER_BANK; // Data pages per bank
  parameter int WordsPerPage    = top_pkg::FLASH_WORDS_PER_PAGE; // Number of flash words per page
  parameter int BusWidth        = top_pkg::TL_DW;
  parameter int MpRegions       = 8;  // flash controller protection regions
  parameter int FifoDepth       = 16; // rd / prog fifos
  parameter int InfoTypesWidth  = prim_util_pkg::vbits(InfoTypes);

  // flash phy parameters
  parameter int DataByteWidth   = prim_util_pkg::vbits(DataWidth / 8);
  parameter int BankW           = prim_util_pkg::vbits(NumBanks);
  parameter int InfoPageW       = prim_util_pkg::vbits((InfosPerBank));
  parameter int PageW           = prim_util_pkg::vbits(PagesPerBank);
  parameter int WordW           = prim_util_pkg::vbits(WordsPerPage);
  parameter int AddrW           = BankW + PageW + WordW; // all flash range
  parameter int BankAddrW       = PageW + WordW;         // 1 bank of flash range
  parameter int AllPagesW       = BankW + PageW;

  // flash ctrl / bus parameters
  // flash / bus width may be different from actual flash word width
  parameter int BusByteWidth    = prim_util_pkg::vbits(BusWidth / 8);
  parameter int WidthMultiple   = DataWidth / BusWidth;
  parameter int BusWordsPerPage = WordsPerPage * WidthMultiple;
  parameter int BusWordW        = prim_util_pkg::vbits(BusWordsPerPage);
  parameter int BusAddrW        = BankW + PageW + BusWordW;
  parameter int BusBankAddrW    = PageW + BusWordW;
  parameter int PhyAddrStart    = BusWordW - WordW;

  // fifo parameters
  parameter int FifoDepthW      = prim_util_pkg::vbits(FifoDepth+1);

  // The end address in bus words for each kind of partition in each bank
  parameter logic [PageW-1:0] DataPartitionEndAddr = PagesPerBank - 1;
  parameter logic [PageW-1:0] InfoPartitionEndAddr [InfoTypes] = '{
    InfoTypeSize[0] - 1,
    InfoTypeSize[1] - 1
  };

  ////////////////////////////
  // All memory protection, seed related parameters
  // Those related for seed pages should be template candidates
  ////////////////////////////

  // parameters for connected components
  parameter int SeedWidth = 256;

  // lcmgr phase enum
  typedef enum logic [1:0] {
    PhaseSeed,
    PhaseRma,
    PhaseNone,
    PhaseInvalid
  } flash_lcmgr_phase_e;

  // alias for super long reg_pkg typedef
  typedef flash_ctrl_reg_pkg::flash_ctrl_reg2hw_bank0_info0_page_cfg_mreg_t info_page_cfg_t;
  typedef flash_ctrl_reg_pkg::flash_ctrl_reg2hw_mp_region_cfg_mreg_t mp_region_cfg_t;

  // memory protection specific structs
  typedef struct packed {
    logic [InfoTypesWidth-1:0] sel;
    logic [AllPagesW-1:0] addr;
  } page_addr_t;

  typedef struct packed {
    page_addr_t           page;
    flash_lcmgr_phase_e   phase;
    info_page_cfg_t       cfg;
  } info_page_attr_t;

  typedef struct packed {
    flash_lcmgr_phase_e   phase;
    mp_region_cfg_t cfg;
  } data_region_attr_t;

  // flash life cycle / key manager management constants
  // One page for creator seeds
  // One page for owner seeds
  parameter int NumSeeds = 2;
  parameter int SeedBank = 0;
  parameter int SeedInfoSel = 0;
  parameter int CreatorSeedIdx = 0;
  parameter int OwnerSeedIdx = 1;
  parameter int CreatorInfoPage = 1;
  parameter int OwnerInfoPage = 2;

  // which page of which info type of which bank
  parameter page_addr_t SeedInfoPageSel [NumSeeds] = '{
    '{
      sel:  SeedInfoSel,
      addr: {SeedBank, CreatorInfoPage}
     },

    '{
      sel:  SeedInfoSel,
      addr: {SeedBank, OwnerInfoPage}
     }
  };

  // hardware interface memory protection rules
  parameter int HwInfoRules = 3;
  parameter int HwDataRules = 1;

  parameter info_page_cfg_t CfgAllowRead = '{
    en:          1'b1,
    rd_en:       1'b1,
    prog_en:     1'b0,
    erase_en:    1'b0,
    scramble_en: 1'b0  // TBD, update to 1 once tb supports ECC
  };

  parameter info_page_cfg_t CfgAllowReadErase = '{
    en:          1'b1,
    rd_en:       1'b1,
    prog_en:     1'b0,
    erase_en:    1'b1,
    scramble_en: 1'b0  // TBD, update to 1 once tb supports ECC
  };

  parameter info_page_attr_t HwInfoPageAttr[HwInfoRules] = '{
    '{
       page:  SeedInfoPageSel[CreatorSeedIdx],
       phase: PhaseSeed,
       cfg:   CfgAllowRead
     },

    '{
       page:  SeedInfoPageSel[OwnerSeedIdx],
       phase: PhaseSeed,
       cfg:   CfgAllowRead
     },

    '{
       page:  SeedInfoPageSel[OwnerSeedIdx],
       phase: PhaseRma,
       cfg:   CfgAllowReadErase
     }
  };

  parameter data_region_attr_t HwDataAttr[HwDataRules] = '{
    '{
       phase: PhaseRma,
       cfg:   '{
                 en:          1'b1,
                 rd_en:       1'b1,
                 prog_en:     1'b0,
                 erase_en:    1'b1,
                 scramble_en: 1'b0,
                 base:        '0,
                 size:        '{default:'1}
                }
     }
  };


  ////////////////////////////
  // Flash operation related enums
  ////////////////////////////

  // Flash Operations Supported
  typedef enum logic [1:0] {
    FlashOpRead     = 2'h0,
    FlashOpProgram  = 2'h1,
    FlashOpErase    = 2'h2,
    FlashOpInvalid  = 2'h3
  } flash_op_e;

  // Flash Program Operations Supported
  typedef enum logic {
    FlashProgNormal = 0,
    FlashProgRepair = 1
  } flash_prog_e;
  parameter int ProgTypes = 2;

  // Flash Erase Operations Supported
  typedef enum logic  {
    FlashErasePage  = 0,
    FlashEraseBank  = 1
  } flash_erase_e;

  // Flash function select
  typedef enum logic [1:0] {
    NoneSel,
    SwSel,
    HwSel
  } flash_sel_e;

  // Flash tlul to fifo direction
  typedef enum logic  {
    WriteDir     = 1'b0,
    ReadDir      = 1'b1
  } flash_flfo_dir_e;

  // Flash partition type
  typedef enum logic {
    FlashPartData = 1'b0,
    FlashPartInfo = 1'b1
  } flash_part_e;

  // Flash controller to memory
  typedef struct packed {
    logic                 req;
    logic                 scramble_en;
    logic                 rd;
    logic                 prog;
    logic                 pg_erase;
    logic                 bk_erase;
    flash_part_e          part;
    logic [BusAddrW-1:0]  addr;
    logic [BusWidth-1:0]  prog_data;
    logic                 prog_last;
    flash_prog_e          prog_type;
    mp_region_cfg_t [MpRegions:0] region_cfgs;
    logic [127:0]         addr_key;
    logic [127:0]         data_key;
  } flash_req_t;

  // default value of flash_req_t (for dangling ports)
  parameter flash_req_t FLASH_REQ_DEFAULT = '{
    req:         1'b0,
    scramble_en: 1'b0,
    rd:          1'b0,
    prog:        1'b0,
    pg_erase:    1'b0,
    bk_erase:    1'b0,
    part:        FlashPartData,
    addr:        '0,
    prog_data:   '0,
    prog_last:   '0,
    prog_type:   FlashProgNormal,
    region_cfgs: '0,
    addr_key:    128'hDEADBEEFBEEFFACEDEADBEEF5A5AA5A5,
    data_key:    128'hDEADBEEF5A5AA5A5DEADBEEFBEEFFACE
  };

  // memory to flash controller
  typedef struct packed {
    logic [ProgTypes-1:0] prog_type_avail;
    logic                rd_done;
    logic                prog_done;
    logic                erase_done;
    logic                rd_err;
    logic [BusWidth-1:0] rd_data;
    logic                init_busy;
  } flash_rsp_t;

  // default value of flash_rsp_t (for dangling ports)
  parameter flash_rsp_t FLASH_RSP_DEFAULT = '{
    prog_type_avail: '{default: '1},
    rd_done:    1'b0,
    prog_done:  1'b0,
    erase_done: 1'b0,
    rd_err:     '0,
    rd_data:    '0,
    init_busy:  1'b0
  };

  ////////////////////////////
  // The following inter-module should be moved to OTP/LC
  ////////////////////////////

  // otp to flash_ctrl
  typedef struct packed {
    logic [127:0] addr_key;
    logic [127:0] data_key;
    // TBD: this signal will become multi-bit in the future
    logic seed_valid;
    logic prog_repair_en;
  } otp_flash_t;

  // lc to flash_ctrl
  typedef struct packed {
    // TBD: this signal will become multi-bit in the future
    logic rma_req;
    logic [BusWidth-1:0] rma_req_token;
    logic provision_en;
  } lc_flash_req_t;

  // flash_ctrl to lc
  typedef struct packed {
    logic rma_ack;
    logic [BusWidth-1:0] rma_ack_token;
  } lc_flash_rsp_t;

  // flash_ctrl to keymgr
  typedef struct packed {
    logic [NumSeeds-1:0][SeedWidth-1:0] seeds;
  } keymgr_flash_t;

  // place holder for interface to EDN, replace with real one later
  typedef struct packed {
    logic valid;
    logic [3:0] entropy;
  } edn_entropy_t;

  // default value of otp_flash_t
  // These are hardwired default values that should never be used.
  // Real values are individualized and supplied from OTP.
  parameter otp_flash_t OTP_FLASH_DEFAULT = '{
    addr_key: 128'hDEADBEEFBEEFFACEDEADBEEF5A5AA5A5,
    data_key: 128'hDEADBEEF5A5AA5A5DEADBEEFBEEFFACE,
    seed_valid: 1'b1,
    prog_repair_en: 1'b1
  };

  parameter lc_flash_req_t LC_FLASH_REQ_DEFAULT = '{
    rma_req: 1'b0,
    rma_req_token: '0,
    provision_en: 1'b1
  };

  parameter edn_entropy_t EDN_ENTROPY_DEFAULT = '{
    valid: 1'b1,
    entropy: '0
  };


  // find the max number pages among info types
  function automatic integer max_info_pages(int infos[InfoTypes]);
    int current_max = 0;
    for (int i = 0; i < InfoTypes; i++) begin
      if (infos[i] > current_max) begin
        current_max = infos[i];
      end
    end
    return current_max;
  endfunction // max_info_banks


endpackage : flash_ctrl_pkg
