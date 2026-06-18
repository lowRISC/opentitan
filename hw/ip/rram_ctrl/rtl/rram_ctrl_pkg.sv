// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// RRAM Controller Package
//

package rram_ctrl_pkg;

  /////////////////////
  // RRAM parameters //
  /////////////////////

  parameter int unsigned TotalBytes      = 2*1024*1024; // 2 MiB
  parameter int unsigned TotalInfoBytes  = 4*1024; // 4 KiB
  parameter int unsigned TotalOtpBytes   = 2*1024 + 512; // (2 KiB + 0.5 KiB integrity)
  parameter int unsigned DataWidth       = 128; // 1 RRAM word in bits
  parameter int unsigned WordsPerPage    = 32; // Number of RRAM words per page
  parameter int unsigned TotalPages      = TotalBytes / (DataWidth / 8) / WordsPerPage; // 4096
  parameter int unsigned TotalInfoPages  = TotalInfoBytes / (DataWidth / 8) / WordsPerPage; // 8
  parameter int unsigned MaxWrWords      = 32; // max. number of words that can be written at once
  parameter int unsigned OtpPages        = TotalOtpBytes / (DataWidth / 8) / WordsPerPage; // 5
  parameter int unsigned DataPages       = TotalPages - OtpPages; // 4091
  parameter int unsigned OtpStartPage    = DataPages;

  parameter int unsigned BusWidth        = top_pkg::TL_DW;
  parameter int unsigned BusIntgWidth    = tlul_pkg::DataIntgWidth;
  parameter int unsigned BusFullWidth    = BusWidth + BusIntgWidth;

  parameter int unsigned MpRegions       = 8;  // controller protection regions
  parameter int unsigned TotalMpRegions  = MpRegions + 2; // + default region and init region

  // RRAM phy parameters
  parameter int unsigned DataByteWidth   = prim_util_pkg::vbits(DataWidth / 8);
  parameter int unsigned PageW           = prim_util_pkg::vbits(TotalPages);
  parameter int unsigned InfoPageW       = prim_util_pkg::vbits(TotalInfoPages);
  parameter int unsigned WordW           = prim_util_pkg::vbits(WordsPerPage);
  parameter int unsigned AddrW           = PageW + WordW; // full RRAM range

  // RRAM ctrl / bus parameters
  parameter int unsigned BusBytes        = BusWidth / 8;
  parameter int unsigned BusByteWidth    = prim_util_pkg::vbits(BusBytes);
  parameter int unsigned WidthMultiple   = DataWidth / BusWidth;
  parameter int unsigned WordSelW        = prim_util_pkg::vbits(WidthMultiple);
  // Maximum number of bus words that can be written at once
  parameter int unsigned BusWordsPerPage = WordsPerPage * WidthMultiple;
  parameter int unsigned BusWordW        = prim_util_pkg::vbits(BusWordsPerPage);
  parameter int unsigned BusAddrW        = PageW + BusWordW;
  parameter int unsigned BusAddrByteW    = BusAddrW + BusByteWidth;

  ////////////////////////////////////////////////////////
  // RRAM Controller related parameters and definitions //
  ////////////////////////////////////////////////////////

  parameter int unsigned CtrlMaxWords  = 1024;
  parameter int unsigned CtrlMaxWordsW = prim_util_pkg::vbits(CtrlMaxWords);

  parameter int unsigned MaxFifoDepth = 16;
  parameter int unsigned MaxFifoWidth = prim_util_pkg::vbits(MaxFifoDepth+1);

  // RRAM disable usage
  typedef enum logic [3:0] {
    PhyDisableIdx,
    ArbFsmDisableIdx,
    LcMgrDisableIdx,
    MpDisableIdx,
    HostDisableIdx,
    IFetchDisableIdx,
    RdFifoIdx,
    WrFifoIdx,
    RramDisableLast
  } rram_disable_pos_e;

  // RRAM Operations Supported
  typedef enum logic [1:0] {
    RramOpRead    = 2'h0,
    RramOpWrite   = 2'h1,
    RramOpRewrite = 2'h2
  } rram_op_e;

  // phase enum (only used by lcmgr at the moment)
  typedef enum logic [1:0] {
    PhaseSeed,
    PhaseRma,
    PhaseNone,
    PhaseInvalid
  } rram_phase_e;

  // RRAM function select
  typedef enum logic [2:0] {
    NoneSel,
    SwSel,
    HwOtpSel,
    HwLcMgrSel,
    HwLoopBack
  } rram_sel_e;

  // RRAM partition type
  typedef enum logic {
    RramPartData = 1'b0,
    RramPartInfo = 1'b1
  } rram_part_e;

  // Error bit positioning
  typedef struct packed {
    logic invalid_op_err;
    logic mp_err;
    logic rd_err;
    logic wr_err;
  } rram_ctrl_err_t;

  // interrupt bit positioning
  typedef enum logic [2:0] {
    WrEmpty,
    WrLvl,
    RdFull,
    RdLvl,
    OpDone,
    CorrErr,
    LastIntrIdx
  } rram_ctrl_intr_e;

  /////////////////////////////////
  // OTP plug related parameters //
  /////////////////////////////////

  parameter int unsigned OtpIntgDataWidth = 64;
  parameter int unsigned OtpIntgWidth = 8;

  ///////////////////////////////////
  // LCMGR plug related parameters //
  ///////////////////////////////////

  parameter int unsigned NumSeeds       = 2;
  parameter int unsigned SeedWidth      = 256;
  parameter int unsigned KeyWidth       = 128;
  parameter int unsigned TotalSeedWidth = SeedWidth * NumSeeds;

  typedef logic [TotalSeedWidth-1:0] all_seeds_t;
  typedef logic [KeyWidth-1:0]       rram_key_t;

  // rram_ctrl to keymgr
  typedef struct packed {
    logic [NumSeeds-1:0][SeedWidth-1:0] seeds;
  } keymgr_rram_t;

  parameter keymgr_rram_t KEYMGR_RRAM_DEFAULT = '{
    seeds:'{
      256'h16c60598_e7d9c867_1aa74d45_6b10dfb4_309ee153_a448b2bb_438ff7ec_d09d21eb,
      256'h9a90bd5d_b04641d6_4f18fc47_b6db3da0_cad2e288_01fec9f5_78f64a12_2f776685
    }
  };

  // These LFSR parameters have been generated with
  // $ ./util/design/gen-lfsr-seed.py --width 32 --seed 1294753918 --prefix ""
  parameter int LfsrWidth = 32;
  typedef logic [LfsrWidth-1:0] lfsr_seed_t;
  typedef logic [LfsrWidth-1:0][$clog2(LfsrWidth)-1:0] lfsr_perm_t;
  parameter lfsr_seed_t RndCnstLfsrSeedDefault = {
    32'h72570dd9
  };
  parameter lfsr_perm_t RndCnstLfsrPermDefault = {
    160'h3d303bb0_990bca04_6f8275be_6ecfd586_9728a92d
  };

  // Design time constants
  parameter rram_key_t RndCnstAddrKeyDefault =
    128'h5d707f8a2d01d400928fa691c6a6e0a4;
  parameter rram_key_t RndCnstDataKeyDefault =
    128'h39953618f2ca6f674af39f64975ea1f5;
  parameter all_seeds_t RndCnstAllSeedsDefault = {
    256'h3528874c0d9e481ead4d240eb6238a2c6218896f5315edb5ccefe029a6d04091,
    256'h9cde77e25a313a76984ab0ebf990983432b03b48186dcd556565fe721b447477
  };

  //////////////////////////////////////////////////////////
  // Open-Source interface RRAM macro <-> RRAM controller //
  //////////////////////////////////////////////////////////

  typedef struct packed {
    logic                 rd_req;
    logic                 wr_req;
    logic                 wr_last;
    logic [AddrW-1:0]     addr;
    logic [DataWidth-1:0] wr_data;
    rram_part_e           part;
    logic                 ecc_en;
  } rram_macro_req_t;

  typedef struct packed {
    logic                 ack;
    logic                 done;
    logic                 err;
    logic                 ecc_err;
    logic [DataWidth-1:0] rd_data;
    logic                 init_done;
    logic                 fatal_err;
    logic                 recov_err;
  } rram_macro_rsp_t;

  ///////////////////////////////////
  // Memory protection definitions //
  ///////////////////////////////////

  import rram_ctrl_reg_pkg::rram_ctrl_reg2hw_mp_region_mreg_t;
  import rram_ctrl_reg_pkg::rram_ctrl_reg2hw_mp_region_cfg_mreg_t;
  import rram_ctrl_reg_pkg::rram_ctrl_reg2hw_default_region_reg_t;
  import rram_ctrl_reg_pkg::rram_ctrl_reg2hw_info_page_cfg_mreg_t;

  typedef rram_ctrl_reg2hw_mp_region_mreg_t sw_region_t;
  typedef rram_ctrl_reg2hw_mp_region_cfg_mreg_t sw_region_cfg_t;
  typedef rram_ctrl_reg2hw_default_region_reg_t sw_default_cfg_t;
  typedef rram_ctrl_reg2hw_info_page_cfg_mreg_t sw_info_cfg_t;

  import prim_mubi_pkg::mubi4_t;
  import prim_mubi_pkg::MuBi4True;
  import prim_mubi_pkg::MuBi4False;

  typedef struct packed {
    mubi4_t en;
    mubi4_t rd_en;
    mubi4_t wr_en;
    mubi4_t scramble_en;
    mubi4_t ecc_en;
    mubi4_t addr_xor_en;
  } page_cfg_t;

  typedef struct packed {
    logic [PageW-1:0] base;
    logic [PageW-1:0] size; // #pages-1
    rram_phase_e      phase;
    page_cfg_t        cfg;
  } mp_region_cfg_t;

  typedef struct packed {
    logic [InfoPageW-1:0] page;
    rram_phase_e          phase;
    page_cfg_t            cfg;
  } mp_info_cfg_t;

  // life cycle / key manager management constants
  // One page for creator seeds
  // One page for owner seeds
  // One page for isolated rram page
  parameter bit [InfoPageW-1:0] CreatorInfoPage  = 5;
  parameter bit [InfoPageW-1:0] OwnerInfoPage    = 6;
  parameter bit [InfoPageW-1:0] IsolatedInfoPage = 7;

  // hardware interface memory protection rules
  parameter int unsigned HwLcMgrInfoRules = 5;
  parameter int unsigned HwLcMgrDataRules = 1;
  parameter int unsigned HwOtpDataRules   = 1;
  parameter int unsigned HostDataRules    = 1;

  parameter page_cfg_t CfgAllowRd = '{
    en:          MuBi4True,
    rd_en:       MuBi4True,
    wr_en:       MuBi4False,
    scramble_en: MuBi4True,
    ecc_en:      MuBi4True,
    addr_xor_en: MuBi4True
  };

  parameter page_cfg_t CfgAllowRdWr = '{
    en:          MuBi4True,
    rd_en:       MuBi4True,
    wr_en:       MuBi4True,
    scramble_en: MuBi4True,
    ecc_en:      MuBi4True,
    addr_xor_en: MuBi4True
  };

  parameter page_cfg_t CfgAllowRdWrOtp = '{
    en:          MuBi4True,
    rd_en:       MuBi4True,
    wr_en:       MuBi4True,
    scramble_en: MuBi4False,
    ecc_en:      MuBi4True,
    addr_xor_en: MuBi4False
  };

  parameter page_cfg_t CfgDisable = '{
    en:          MuBi4False,
    rd_en:       MuBi4False,
    wr_en:       MuBi4False,
    scramble_en: MuBi4False,
    ecc_en:      MuBi4False,
    addr_xor_en: MuBi4False
  };

  parameter page_cfg_t CfgNoAccess = '{
    en:          MuBi4True,
    rd_en:       MuBi4False,
    wr_en:       MuBi4False,
    scramble_en: MuBi4False,
    ecc_en:      MuBi4False,
    addr_xor_en: MuBi4False
  };

  parameter page_cfg_t CfgRw = '{
    en:          MuBi4True,
    rd_en:       MuBi4True,
    wr_en:       MuBi4True,
    scramble_en: MuBi4False,
    ecc_en:      MuBi4True,
    addr_xor_en: MuBi4True
  };

  parameter mp_info_cfg_t HwLcMgrInfoPageCfg[HwLcMgrInfoRules] = '{
    '{
      page:  CreatorInfoPage,
      phase: PhaseSeed,
      cfg:   CfgAllowRd
    },

    '{
      page:  OwnerInfoPage,
      phase: PhaseSeed,
      cfg:   CfgAllowRd
    },

    '{
      page:  CreatorInfoPage,
      phase: PhaseRma,
      cfg:   CfgAllowRdWr
    },

    '{
      page:  OwnerInfoPage,
      phase: PhaseRma,
      cfg:   CfgAllowRdWr
    },

    '{
      page:  IsolatedInfoPage,
      phase: PhaseRma,
      cfg:   CfgAllowRdWr
    }
  };

  // data pages are wiped by RMA request
  parameter mp_region_cfg_t HwLcMgrDataCfg[HwLcMgrDataRules] = '{
    '{
      phase: PhaseRma,
      cfg:   CfgAllowRdWr,
      base:  '0,
      size:  DataPages-1
    }
  };

  // RD/WR access to OTP space, everything else is disabled
  parameter mp_region_cfg_t HwOtpDataCfg[HwOtpDataRules] = '{
    '{
      phase: PhaseInvalid,
      cfg:   CfgAllowRdWrOtp,
      base:  PageW'(OtpStartPage),
      size:  OtpPages-1
    }
  };

  // RD/WR access to OTP space, everything else is disabled
  parameter mp_region_cfg_t SwInitDataCfg = '{
    phase: PhaseInvalid,
    cfg:   CfgNoAccess,
    base:  PageW'(OtpStartPage),
    size:  OtpPages-1
  };

  // which page of which info type of which bank for seed selection
  parameter logic [InfoPageW-1:0] SeedInfoPageSel [NumSeeds] = '{
    CreatorInfoPage,
    OwnerInfoPage
  };

  // RMA entries
  typedef struct packed {
    rram_part_e       part;
    logic [PageW-1:0] base;
    logic [PageW-1:0] size; // #pages-1
  } rma_wipe_entry_t;

  // entries to be wiped at RMA
  parameter int unsigned     WipeEntries = 4;
  parameter rma_wipe_entry_t RmaWipeEntries[WipeEntries] = '{
    '{
       part: RramPartInfo,
       base: PageW'(CreatorInfoPage),
       size: 0
     },
    '{
       part: RramPartInfo,
       base: PageW'(OwnerInfoPage),
       size: 0
     },
    '{
       part: RramPartInfo,
       base: PageW'(IsolatedInfoPage),
       size: 0
     },
    '{
       part: RramPartData,
       base: '0,
       size: DataPages-1
     }
  };

  //////////////////////////////////
  // RRAM phy specific parameters //
  //////////////////////////////////

  parameter int unsigned NumRdBuf = 4;
  parameter int unsigned NumOutstandingRdReq = 2;

  // Read buffer metadata
  typedef enum logic [1:0] {
    Invalid  = 2'h0,
    Alloc    = 2'h1,
    Valid    = 2'h2,
    Verified = 2'h3
  } rd_buf_attr_e;

  typedef struct packed {
    logic [WidthMultiple-1:0][BusFullWidth-1:0] data;
    logic [AddrW-1:0]                           addr;
    logic                                       descramble_en;
    logic                                       ecc_en;
    logic                                       addr_xor_en;
    rram_part_e                                 part;
    rd_buf_attr_e                               attr;
    logic                                       err;
  } rd_buf_t;

  typedef struct packed {
    logic                 err;
    logic [DataWidth-1:0] data;
  } rd_rsp_entry_t;
  parameter int unsigned RdRspFifoWidth = $bits(rd_rsp_entry_t);

  typedef struct packed {
    logic [NumRdBuf-1:0] buf_sel;
    logic                update;
    logic                verify;
    logic [WordSelW-1:0] word_sel;
    logic [6:0]          cmd_intg;
  } meta_entry_t;
  parameter int unsigned MetaFifoWidth = $bits(meta_entry_t);

  //////////////////////////////////
  // Scrambling block definitions //
  //////////////////////////////////

  // scramble / de-scramble parameters
  parameter int unsigned KeySize       = KeyWidth;
  // Number of cycles the gf_mult is given to complete
  parameter int unsigned GfMultCycles  = 4;
  // Register the inputs for the mask computation with the gfmult
  parameter int unsigned MaskReqReg    = 0;
  parameter int unsigned CipherWidth   = 64;

  // GF(2) irreducible polynomial for RRAM XEX scrambling scheme.
  // We use the NIST 800-38B recommendation for block cipher modes of operation.
  // See Section "5.3 Subkeys" on page 6:
  // https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-38B.pdf
  // Specifically, we use the polynomial: x^128 + x^7 + x^2 + x + 1.
  parameter bit [DataWidth-1:0] ScrambleIPoly = DataWidth'(1'b1) << 7 |
                                                DataWidth'(1'b1) << 2 |
                                                DataWidth'(1'b1) << 1 |
                                                DataWidth'(1'b1) << 0;

  typedef enum logic {
    ScrambleOp   = 1'b0,
    DeScrambleOp = 1'b1
  } cipher_ops_e;

  typedef struct packed {
    logic                 calc_req;
    logic                 op_req;
    cipher_ops_e          op_type;
    logic                 cipher_switch;
    logic [AddrW-1:0]     addr;
    logic [DataWidth-1:0] data_in;
  } scramble_req_t;

  typedef struct packed {
    logic                 calc_ack;
    logic                 op_ack;
    logic [DataWidth-1:0] mask;
    logic [DataWidth-1:0] data_out;
  } scramble_rsp_t;

endpackage : rram_ctrl_pkg
