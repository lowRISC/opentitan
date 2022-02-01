// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash Controller module.
//

package flash_ctrl_pkg;

  // design parameters that can be altered through topgen
  parameter int unsigned NumBanks        = flash_ctrl_reg_pkg::RegNumBanks;
  parameter int unsigned PagesPerBank    = flash_ctrl_reg_pkg::RegPagesPerBank;
  parameter int unsigned BusPgmResBytes  = flash_ctrl_reg_pkg::RegBusPgmResBytes;

  // fixed parameters of flash derived from topgen parameters
  parameter int DataWidth       = 64;
  parameter int MetaDataWidth   = 12;
  parameter int InfoTypes       = 3; // How many types of info per bank

// The following hard-wired values are there to work-around verilator.
// For some reason if the values are assigned through parameters verilator thinks
// they are not constant
  parameter int InfoTypeSize [InfoTypes] = '{
    10,
    1,
    2
  };
  parameter int InfosPerBank    = max_info_pages('{
    10,
    1,
    2
  });
  parameter int WordsPerPage    = 256; // Number of flash words per page
  parameter int BusWidth        = top_pkg::TL_DW;
  parameter int MpRegions       = 8;  // flash controller protection regions
  parameter int FifoDepth       = 16; // rd / prog fifos
  parameter int InfoTypesWidth  = prim_util_pkg::vbits(InfoTypes);

  // flash phy parameters
  parameter int DataByteWidth   = prim_util_pkg::vbits(DataWidth / 8);
  parameter int BankW           = prim_util_pkg::vbits(NumBanks);
  parameter int InfoPageW       = prim_util_pkg::vbits(InfosPerBank);
  parameter int PageW           = prim_util_pkg::vbits(PagesPerBank);
  parameter int WordW           = prim_util_pkg::vbits(WordsPerPage);
  parameter int AddrW           = BankW + PageW + WordW; // all flash range
  parameter int BankAddrW       = PageW + WordW;         // 1 bank of flash range
  parameter int AllPagesW       = BankW + PageW;

  // flash ctrl / bus parameters
  // flash / bus width may be different from actual flash word width
  parameter int BusBytes        = BusWidth / 8;
  parameter int BusByteWidth    = prim_util_pkg::vbits(BusBytes);
  parameter int WidthMultiple   = DataWidth / BusWidth;
  // Number of bus words that can be programmed at once
  parameter int BusPgmRes       = BusPgmResBytes / BusBytes;
  parameter int BusPgmResWidth  = prim_util_pkg::vbits(BusPgmRes);
  parameter int BusWordsPerPage = WordsPerPage * WidthMultiple;
  parameter int BusWordW        = prim_util_pkg::vbits(BusWordsPerPage);
  parameter int BusAddrW        = BankW + PageW + BusWordW;
  parameter int BusAddrByteW    = BusAddrW + BusByteWidth;
  parameter int BusBankAddrW    = PageW + BusWordW;
  parameter int PhyAddrStart    = BusWordW - WordW;


  // fifo parameters
  parameter int FifoDepthW      = prim_util_pkg::vbits(FifoDepth+1);

  // The end address in bus words for each kind of partition in each bank
  parameter logic [PageW-1:0] DataPartitionEndAddr = PageW'(PagesPerBank - 1);
  //parameter logic [PageW-1:0] InfoPartitionEndAddr [InfoTypes] = '{
  //  9,
  //  0,
  //  1
  //};
  parameter logic [PageW-1:0] InfoPartitionEndAddr [InfoTypes] = '{
    PageW'(InfoTypeSize[0] - 1),
    PageW'(InfoTypeSize[1] - 1),
    PageW'(InfoTypeSize[2] - 1)
  };

  ////////////////////////////
  // All memory protection, seed related parameters
  // Those related for seed pages should be template candidates
  ////////////////////////////

  // parameters for connected components
  parameter int SeedWidth = 256;
  parameter int KeyWidth  = 128;
  parameter int EdnWidth  = edn_pkg::ENDPOINT_BUS_WIDTH;
  typedef logic [KeyWidth-1:0] flash_key_t;

  // Default Lfsr configurations
  // These LFSR parameters have been generated with
  // $ util/design/gen-lfsr-seed.py --width 32 --seed 1274809145 --prefix ""
  parameter int LfsrWidth = 32;
  typedef logic [LfsrWidth-1:0] lfsr_seed_t;
  typedef logic [LfsrWidth-1:0][$clog2(LfsrWidth)-1:0] lfsr_perm_t;
  parameter lfsr_seed_t RndCnstLfsrSeedDefault = 32'ha8cee782;
  parameter lfsr_perm_t RndCnstLfsrPermDefault = {
    160'hd60bc7d86445da9347e0ccdd05b281df95238bb5
  };

  // These LFSR parameters have been generated with
  // $ util/design/gen-lfsr-seed.py --width 64 --seed 691876113 --prefix ""


  // lcmgr phase enum
  typedef enum logic [1:0] {
    PhaseSeed,
    PhaseRma,
    PhaseNone,
    PhaseInvalid
  } flash_lcmgr_phase_e;

  import flash_ctrl_reg_pkg::flash_ctrl_reg2hw_mp_bank_cfg_shadowed_mreg_t;
  import flash_ctrl_reg_pkg::flash_ctrl_reg2hw_mp_region_cfg_shadowed_mreg_t;
  import flash_ctrl_reg_pkg::flash_ctrl_reg2hw_bank0_info0_page_cfg_shadowed_mreg_t;
  import flash_ctrl_reg_pkg::flash_ctrl_reg2hw_default_region_shadowed_reg_t;

  typedef flash_ctrl_reg2hw_mp_bank_cfg_shadowed_mreg_t sw_bank_cfg_t;
  typedef flash_ctrl_reg2hw_mp_region_cfg_shadowed_mreg_t sw_region_cfg_t;
  typedef flash_ctrl_reg2hw_default_region_shadowed_reg_t sw_default_cfg_t;
  typedef flash_ctrl_reg2hw_bank0_info0_page_cfg_shadowed_mreg_t sw_info_cfg_t;

  // alias for super long reg_pkg typedef
  typedef struct packed {
    logic        q;
  } bank_cfg_t;

  // This is identical to the reg structures but do not have err_updates / storage
  typedef struct packed {
    struct packed {
      logic        q;
    } en;
    struct packed {
      logic        q;
    } rd_en;
    struct packed {
      logic        q;
    } prog_en;
    struct packed {
      logic        q;
    } erase_en;
    struct packed {
      logic        q;
    } scramble_en;
    struct packed {
      logic        q;
    } ecc_en;
    struct packed {
      logic        q;
    } he_en;
  } info_page_cfg_t;

  // This is identical to the reg structures but do not have err_updates / storage
  typedef struct packed {
    struct packed {
      logic        q;
    } en;
    struct packed {
      logic        q;
    } rd_en;
    struct packed {
      logic        q;
    } prog_en;
    struct packed {
      logic        q;
    } erase_en;
    struct packed {
      logic        q;
    } scramble_en;
    struct packed {
      logic        q;
    } ecc_en;
    struct packed {
      logic        q;
    } he_en;
    struct packed {
      logic [8:0]  q;
    } base;
    struct packed {
      logic [9:0] q;
    } size;
  } mp_region_cfg_t;

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
  // One page for isolated flash page
  parameter int NumSeeds = 2;
  parameter bit [BankW-1:0] SeedBank = 0;
  parameter bit [InfoTypesWidth-1:0] SeedInfoSel = 0;
  parameter bit [0:0] CreatorSeedIdx = 0;
  parameter bit [0:0] OwnerSeedIdx = 1;
  parameter bit [PageW-1:0] CreatorInfoPage = 1;
  parameter bit [PageW-1:0] OwnerInfoPage = 2;
  parameter bit [PageW-1:0] IsolatedInfoPage = 3;

  // which page of which info type of which bank for seed selection
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

  // which page of which info type of which bank for isolated partition
  parameter page_addr_t IsolatedPageSel = '{
    sel:  SeedInfoSel,
    addr: {SeedBank, IsolatedInfoPage}
  };

  // hardware interface memory protection rules
  parameter int HwInfoRules = 5;
  parameter int HwDataRules = 1;

  parameter info_page_cfg_t CfgAllowRead = '{
    en:          1'b1,
    rd_en:       1'b1,
    prog_en:     1'b0,
    erase_en:    1'b0,
    scramble_en: 1'b0,
    ecc_en:      1'b0, // TBD, update to 1 once tb supports ECC
    he_en:       1'b1
  };

  parameter info_page_cfg_t CfgAllowReadProgErase = '{
    en:          1'b1,
    rd_en:       1'b1,
    prog_en:     1'b1,
    erase_en:    1'b1,
    scramble_en: 1'b1,
    ecc_en:      1'b1,
    he_en:       1'b1   // HW assumes high endurance
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
       page:  SeedInfoPageSel[CreatorSeedIdx],
       phase: PhaseRma,
       cfg:   CfgAllowReadProgErase
     },

    '{
       page:  SeedInfoPageSel[OwnerSeedIdx],
       phase: PhaseRma,
       cfg:   CfgAllowReadProgErase
     },

    '{
       page:  IsolatedPageSel,
       phase: PhaseRma,
       cfg:   CfgAllowReadProgErase
     }
  };

  parameter data_region_attr_t HwDataAttr[HwDataRules] = '{
    '{
       phase: PhaseRma,
       cfg:   '{
                 en:          1'b1,
                 rd_en:       1'b1,
                 prog_en:     1'b1,
                 erase_en:    1'b1,
                 scramble_en: 1'b1,
                 ecc_en:      1'b1,
                 he_en:       1'b1, // HW assumes high endurance
                 base:        '0,
                 size:        '1
                }
     }
  };


  ////////////////////////////
  // Design time constants
  ////////////////////////////
  parameter flash_key_t RndCnstAddrKeyDefault =
    128'h5d707f8a2d01d400928fa691c6a6e0a4;
  parameter flash_key_t RndCnstDataKeyDefault =
    128'h39953618f2ca6f674af39f64975ea1f5;

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
    logic                 ecc_en;
    logic                 he_en;
    logic                 rd_buf_en;
    logic                 rd;
    logic                 prog;
    logic                 pg_erase;
    logic                 bk_erase;
    logic                 erase_suspend;
    flash_part_e          part;
    logic [InfoTypesWidth-1:0] info_sel;
    logic [BusAddrW-1:0]  addr;
    logic [BusWidth-1:0]  prog_data;
    logic                 prog_last;
    flash_prog_e          prog_type;
    mp_region_cfg_t [MpRegions:0] region_cfgs;
    logic [KeyWidth-1:0]  addr_key;
    logic [KeyWidth-1:0]  data_key;
    logic [KeyWidth-1:0]  rand_addr_key;
    logic [KeyWidth-1:0]  rand_data_key;
    logic                 alert_trig;
    logic                 alert_ack;
    jtag_pkg::jtag_req_t  jtag_req;
    logic                 intg_err;
    prim_mubi_pkg::mubi4_t flash_disable;
  } flash_req_t;

  // default value of flash_req_t (for dangling ports)
  parameter flash_req_t FLASH_REQ_DEFAULT = '{
    req:           '0,
    scramble_en:   '0,
    ecc_en:        '0,
    he_en:         '0,
    rd_buf_en:     1'b0,
    rd:            '0,
    prog:          '0,
    pg_erase:      '0,
    bk_erase:      '0,
    erase_suspend: '0,
    part:          FlashPartData,
    info_sel:      '0,
    addr:          '0,
    prog_data:     '0,
    prog_last:     '0,
    prog_type:     FlashProgNormal,
    region_cfgs:   '0,
    addr_key:      RndCnstAddrKeyDefault,
    data_key:      RndCnstDataKeyDefault,
    rand_addr_key: '0,
    rand_data_key: '0,
    alert_trig:    1'b0,
    alert_ack:     1'b0,
    jtag_req:      '0,
    intg_err:      '0,
    flash_disable: prim_mubi_pkg::MuBi4False
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
    logic                flash_err;
    logic [NumBanks-1:0] ecc_single_err;
    logic [NumBanks-1:0][BusAddrW-1:0] ecc_addr;
    jtag_pkg::jtag_rsp_t jtag_rsp;
    logic                intg_err;
  } flash_rsp_t;

  // default value of flash_rsp_t (for dangling ports)
  parameter flash_rsp_t FLASH_RSP_DEFAULT = '{
    prog_type_avail:    {ProgTypes{1'b1}},
    rd_done:            1'b0,
    prog_done:          1'b0,
    erase_done:         1'b0,
    rd_err:             '0,
    rd_data:            '0,
    init_busy:          1'b0,
    flash_err:          1'b0,
    ecc_single_err:     '0,
    ecc_addr:           '0,
    jtag_rsp:           '0,
    intg_err:           '0
  };

  // RMA entries
  typedef struct packed {
    logic [BankW-1:0] bank;
    flash_part_e part;
    logic [InfoTypesWidth-1:0] info_sel;
    logic [PageW:0] start_page;
    logic [PageW:0] num_pages;
  } rma_wipe_entry_t;

  // entries to be wiped
  parameter int WipeEntries = 5;
  parameter rma_wipe_entry_t RmaWipeEntries[WipeEntries] = '{
    '{
       bank: SeedBank,
       part: FlashPartInfo,
       info_sel: SeedInfoSel,
       start_page: {1'b0, CreatorInfoPage},
       num_pages: 1
     },

    '{
       bank: SeedBank,
       part: FlashPartInfo,
       info_sel: SeedInfoSel,
       start_page: {1'b0, OwnerInfoPage},
       num_pages: 1
     },

    '{
       bank: SeedBank,
       part: FlashPartInfo,
       info_sel: SeedInfoSel,
       start_page: {1'b0, IsolatedInfoPage},
       num_pages: 1
     },

    '{
       bank: 0,
       part: FlashPartData,
       info_sel: 0,
       start_page: 0,
       num_pages: (PageW + 1)'(PagesPerBank)
     },

    '{
       bank: 1,
       part: FlashPartData,
       info_sel: 0,
       start_page: 0,
       num_pages: (PageW + 1)'(PagesPerBank)
     }
  };


  // flash_ctrl to keymgr
  typedef struct packed {
    logic [NumSeeds-1:0][SeedWidth-1:0] seeds;
  } keymgr_flash_t;

  parameter keymgr_flash_t KEYMGR_FLASH_DEFAULT = '{
    seeds: '{
     256'h9152e32c9380a4bcc3e0ab263581e6b0e8825186e1e445631646e8bef8c45d47,
     256'hfa365df52da48cd752fb3a026a8e608f0098cfe5fa9810494829d0cd9479eb78
    }
  };

  // dft_en jtag selection
  typedef enum logic [2:0] {
    FlashLcTckSel,
    FlashLcTdiSel,
    FlashLcTmsSel,
    FlashLcTdoSel,
    FlashBistSel,
    FlashLcDftLast
  } flash_lc_jtag_e;

  // Error bit positioning
  typedef struct packed {
    logic oob_err;
    logic mp_err;
    logic rd_err;
    logic prog_win_err;
    logic prog_type_err;
    logic phy_err;
  } flash_ctrl_err_t;

  // interrupt bit positioning
  typedef enum logic[2:0] {
    ProgEmpty,
    ProgLvl,
    RdFull,
    RdLvl,
    OpDone,
    CorrErr,
    LastIntrIdx
  } flash_ctrl_intr_e;

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

  // RMA control FSM encoding
  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 7 -n 10   //      -s 3319803877 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||||||| (47.62%)
  //  6: |||||||||||||||| (38.10%)
  //  7: |||| (9.52%)
  //  8: || (4.76%)
  //  9: --
  // 10: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 8
  // Minimum Hamming weight: 3
  // Maximum Hamming weight: 6
  //
  localparam int RmaStateWidth = 10;
  typedef enum logic [RmaStateWidth-1:0] {
    StRmaIdle        = 10'b1101000011,
    StRmaPageSel     = 10'b0010111001,
    StRmaErase       = 10'b1111010100,
    StRmaEraseWait   = 10'b0111010101,
    StRmaWordSel     = 10'b0001011111,
    StRmaProgram     = 10'b0110001110,
    StRmaProgramWait = 10'b1000110110,
    StRmaRdVerify    = 10'b1011101010,
    StRmaInvalid     = 10'b1100101101
  } rma_state_e;

endpackage : flash_ctrl_pkg
