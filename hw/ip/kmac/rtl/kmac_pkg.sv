// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// kmac_pkg

package kmac_pkg;
  parameter int MsgWidth = sha3_pkg::MsgWidth;
  parameter int MsgStrbW = sha3_pkg::MsgStrbW;

  // Message FIFO depth
  //
  // Assume entropy is ready always (if Share is reused as an entropy in Chi)
  // Then it takes 72 cycles to complete the Keccak round. While Keccak is in
  // operation, the module need to store the incoming messages to not degrade
  // the throughput.
  //
  // Based on the observation from HMAC case, the core usually takes 5 clocks
  // to fetch data and store into KMAC. So the core can push at most 14.5 X 4B
  // which is 58B. After that, Keccak can fetch the data from MSG_FIFO faster
  // rate than the core can push. To fetch 58B, it takes around 7~8 cycles.
  // For that time, the core only can push at most 2 DW. After that Keccak
  // waits the incoming message.
  //
  // So Message FIFO doesn't need full block size except the KMAC case, which
  // is delayed the operation by processing Function Name N, customization S,
  // and secret keys. But KMAC doesn't need high throughput anyway (72Mb/s).
  parameter int RegIntfWidth = 32; // 32bit interface
  parameter int RegLatency   = 5;  // 5 cycle to write one Word
  parameter int Sha3Latency  = 72; // Expected masked sha3 processing time 24x3

  // Total required buffer size while SHA3 is in processing
  parameter int BufferCycles   = (Sha3Latency + RegLatency - 1)/RegLatency;
  parameter int BufferSizeBits = RegIntfWidth * BufferCycles;

  // Required MsgFifoDepth. Adding slightly more buffer for margin
  parameter int MsgFifoDepth   = 2 + ((BufferSizeBits + MsgWidth - 1)/MsgWidth);
  parameter int MsgFifoDepthW  = $clog2(MsgFifoDepth+1);

  parameter int MsgWindowWidth = 32; // Register width
  parameter int MsgWindowDepth = 512; // 2kB space

  // Key related definitions
  // If this value is changed, please modify the logic inside kmac_core
  // that assigns the value into `encoded_key`
  parameter int MaxKeyLen = 512;

  // size of encode_string(Key)
  // $ceil($clog2(MaxKeyLen+1)/8)
  parameter int MaxEncodedKeyLenW = $clog2(MaxKeyLen+1);
  parameter int MaxEncodedKeyLenByte = (MaxEncodedKeyLenW + 8 - 1) / 8;
  parameter int MaxEncodedKeyLenSize = MaxEncodedKeyLenByte * 8;

  //                             Secret Key  left_encode(len(Key))
  //                             ----------  ------------------------
  parameter int MaxEncodedKeyW = MaxKeyLen + MaxEncodedKeyLenSize + 8;

  // key_len is SW configurable CSR.
  // Current KMAC allows 5 key length options.
  // This value determines the KMAC core how to map the value
  // from Secret Key register to key size block
  typedef enum logic [2:0] {
    Key128 = 3'b 000, // 128 bit secret key
    Key192 = 3'b 001, // 192 bit secret key
    Key256 = 3'b 010, // 256 bit secret key
    Key384 = 3'b 011, // 384 bit secret key
    Key512 = 3'b 100  // 512 bit secret key
  } key_len_e;


  // SEC_CM: SW_CMD.CTRL.SPARSE
  // kmac_cmd_e defines the possible command sets that software issues via
  // !!CMD register. This is mainly to limit the error scenario that SW writes
  // multiple commands at once. Additionally they are sparse encoded to harden
  // against FI attacks
  //
  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 3 -m 5 -n 6 \
  //      -s 1891656028 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||||||||| (50.00%)
  //  4: |||||||||||||||| (40.00%)
  //  5: |||| (10.00%)
  //  6: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 5
  // Minimum Hamming weight: 3
  // Maximum Hamming weight: 4
  //
  typedef enum logic [5:0] {
    //CmdNone      = 6'b001011, // dec 10
    // CmdNone is manually set to all zero by design!
    // The minimum Hamming distance is still 3
    CmdNone      = 6'b000000, // dec  0
    CmdStart     = 6'b011101, // dec 29
    CmdProcess   = 6'b101110, // dec 46
    CmdManualRun = 6'b110001, // dec 49
    CmdDone      = 6'b010110  // dec 22
  } kmac_cmd_e;

  // Timer
  parameter int unsigned TimerPrescalerW = 10;
  parameter int unsigned EdnWaitTimerW   = 16;

  // Entropy Mode Selection : Should be matched to register package Enum value
  typedef enum logic [1:0] {
    EntropyModeNone = 2'h 0,
    EntropyModeEdn  = 2'h 1,
    EntropyModeSw   = 2'h 2
  } entropy_mode_e;

  // PRNG (kmac_entropy)
  parameter int unsigned EntropyOutputW = 800;
  parameter int unsigned EntropyStateW = 288;

  // These LFSR parameters have been generated with
  // $ ./util/design/gen-lfsr-seed.py --width 288 --seed 31468618 --prefix ""
  typedef logic [EntropyStateW-1:0] lfsr_seed_t;
  parameter lfsr_seed_t RndCnstLfsrSeedDefault = {
    32'h758a4420,
    256'h31e1c461_6ea343ec_153282a3_0c132b57_23c5a4cf_4743b3c7_c32d580f_74f1713a
  };

  // We use a single seed that is split down into chunks internally.
  // These LFSR parameters have been generated with
  // $ ./util/design/gen-lfsr-seed.py --width 800 --seed 3369807298 --prefix ""
  typedef logic [EntropyOutputW-1:0][$clog2(EntropyOutputW)-1:0] lfsr_perm_t;
  parameter lfsr_perm_t RndCnstLfsrPermDefault = {
    64'hb1a3e87aeb4e69f0,
    256'h2d8a6ee2c9ac567b2aa401a639a2a8ea2553614c0a8daf672c06546fc0d35267,
    256'hc4572024bc116458dd0f1c10a8aef5c4ad9a788968d0d7ca7345c6b8f277a5d3,
    256'hec5da20f261826ed3c8992724e70db897060be51b07a96902e14a42d12d320f8,
    256'h187049b6c25f35d0e485cc4b9ef01dad2865b5e558926f380718b74394fe0f82,
    256'hd5395a7d0aa4845af814e8681107a4c793758572c9467493bf1248a48f1b40c2,
    256'h09319b55111d0401819685a43a06f0da441021a8c220b14f01d44e49c1683a82,
    256'hafeb980964aa050641f4205131d9d4741eb5dd658e603b8ed438cb1096628d42,
    256'h62c9d75ced78ed09a3ddbb60f533eef10aa5a54b478d61a06a4b326eb3402105,
    256'hc27d562c6d91b48440d6d06e543be9871628a4aa9b3d2e51fa0ac2eb89a17f6d,
    256'h207ad96caf25d1fcffab210c1aff12252346fe4d56a7cd9b8605c7fa638895a9,
    256'h60158cd3a1ce4f2f6cf5d48579ac14b1e5219ca8914e0507b635dc712554f6bb,
    256'h0ae412943a7596f4644a0c13646adc91d02c406a10d232791d3de9919eec5424,
    256'haa2cac5f556c15c647eb29365062daf6aa848e10b3f665abccca713036d9f1cb,
    256'h1c9bd4aaeb19c5ac01b1805e0d5479860870da49a55e8f386ca8232c728e2f61,
    256'h3007aa420758818e5312401372eaa00d21c70c7e1158d2e08a1b6ac0b820cb67,
    256'hf0ba4b5c0865ff04f0f9d0175817c65d81918e43e14b2f83d574bfa9c6e6deae,
    256'h64c22c2974a1d5c55e2367004b249d5a02fc566685ea33b6f73aaa0244b34412,
    256'hb1a12230adb1748dc1d956f9f10c8e1aa52f4702e06a16680d92226c830ec4ce,
    256'h4c2eead21f08c387c3f1de89eb33b983c748e848f68b54f256715221177c5a4a,
    256'h0a47d82741955626755ba1cc24e2ba40504111b9e26136be714c5bc0d330c3f7,
    256'h75e863de763270a993890d633c6897218e151943edd8b79ae145cf564b774613,
    256'h0b0a76c40e7e84c876640dc78260c09a85e92e5ab56c22c0e72a8669fe88ba10,
    256'h8b99e437c776f0cea0d144f285b6ab7259e12284f380ae3410171cd6a8b04415,
    256'he95081c8c57e3e526ad5b38019a5c1b5505540462157e7c7e68e6a6a16ac460a,
    256'h5d5578da28092c7cc927cb9c0ed614a79b0e32b4c5b6a269a40743bef42b5e29,
    256'hd9a75ecb5548a29e9d34ddda07c8404aabbf5479456731ece3785f6090c3f862,
    256'h6eb1a5119e8b8e56b1455d820b46e20e15bb7d185a636b10ab8565732c59a302,
    256'h329925186604edbd5029a9f865268e90003b5b69d3e99240c3432291a60c62a4,
    256'hebad1ed028cd021b27260db22089e0c44481b1a4c120134ac63dc52fbc4cafb2,
    256'he065add2665fb361665267b53024329d96587d661f724171155ee73a3f0c47a8,
    256'h149751a5903c8bbcaf1782e415dfda531eb2af67c25e190330a12000e1fbb9cd
  };

  // These LFSR parameters have been generated with
  // $ ./util/design/gen-lfsr-seed.py --width 800 --seed 31468618 --prefix "Buffer"
  typedef logic [EntropyOutputW-1:0] buffer_lfsr_seed_t;
  parameter buffer_lfsr_seed_t RndCnstBufferLfsrSeedDefault = {
    32'h292603b4,
    256'hf1d83863_e0bd0634_4544ad28_a91d8668_24b66efd_92ad8123_5381f2bc_3d65392c,
    256'h83c01ea5_d8be84f1_e2588917_11849a07_5a71f35f_e9b31605_f9077a6b_758a4420,
    256'h31e1c461_6ea343ec_153282a3_0c132b57_23c5a4cf_4743b3c7_c32d580f_74f1713a
  };

  // Message permutation
  // These LFSR parameters have been generated with
  // $ ./util/design/gen-lfsr-seed.py --width 64 --seed 1201202158 --prefix ""
  // And changed the type name from lfsr_perm_t to msg_perm_t
  typedef logic [MsgWidth-1:0][$clog2(MsgWidth)-1:0] msg_perm_t;
  parameter msg_perm_t RndCnstMsgPermDefault = {
    128'h382af41849db4cfb9c885f72f118c102,
    256'hcb5526978defac799192f65f54148379af21d7e10d82a5a33c3f31a1eaf964b8
  };

  ///////////////////////////
  // Application interface //
  ///////////////////////////

  // Application interface type. Either use a compile-time defined configuration or the app
  // provides a hashing configuration at runtime.
  typedef enum logic {
    AppStatic  = 1'b0,
    AppDynamic = 1'b1
  } app_type_e;

  // The possible hashing operation for an interface.
  typedef enum logic [1:0] {
    AppSHA3   = 2'b00,
    AppShake  = 2'b01,
    AppCShake = 2'b10,
    AppKMAC   = 2'b11
  } app_mode_e;

  // Predefined encoded_string
  parameter logic [15:0] EncodedStringEmpty   = 16'h                     0001;
  parameter logic [47:0] EncodedStringKMAC    = 48'h           4341_4D4B_2001;
  // encoded_string("LC_CTRL")
  parameter logic [71:0] EncodedStringLcCtrl  = 72'h   4c_5254_435f_434C_3801;
  // encoded_string("ROM_CTRL")
  parameter logic [79:0] EncodedStringRomCtrl = 80'h 4c52_5443_5f4d_4f52_4001;
  parameter int unsigned NSPrefixW = sha3_pkg::NSRegisterSize*8;

  typedef struct packed {
    // PrefixMode determines whether to take the prefix from the CSR or use the hardcoded prefix.
    // For static interfaces, if PrefixMode is 1, the Prefix will be used for both cSHAKE and
    // KMAC operations. If 0, the CSR value is used.
    // For dynamic interfaces, PrefixMode has no direct effect. The prefix is selected depending
    // on the selected mode.
    // If the mode is cSHAKE, it is always the CSR prefix used.
    // If the mode is KMAC, it is always the compile-time value used.
    logic prefix_mode;

    // The hashing mode which is performed.
    app_mode_e mode;

    // The strength of the selected mode.
    sha3_pkg::keccak_strength_e kstrength;

    // If 1, the app interface will automatically trigger a RUN command once it has pushed the
    // full rate on the response channel. If 0, no squeeze can be performed at all and only the
    // first rate is pushed. Usually enabled for SHAKE and cSHAKE and disabled for SHA3 and KMAC.
    // Has no effect on static interfaces.
    logic en_xof;
  } app_ses_config_t;

  // Per default use an invalid configuration.
  parameter app_ses_config_t AppSesCfgDefault = '0;

  typedef struct packed {
    /////////////////////////////////
    // Compile-time configurations //
    /////////////////////////////////

    // Whether the interface is static or dynamic. For static interfaces all configs below are fix.
    // For dynamic interfaces, certain config values are sent as first message part.
    app_type_e if_type;

    // Specify whether the input comes in shares. If set, message FIFO is bypassed. This parameter
    // is only relevant if the EnMasking parameter is set.
    logic masked;

    // A compile-time defined prefix used for cSHAKE or KMAC operations. See PrefixMode when this
    // value is used.
    logic [NSPrefixW-1:0] prefix;

    // If set, non-standard combinations of mode and strength are supported for this dynamic
    // interface. Otherwise a non-standard combination will result in a service rejected error.
    logic en_unsup_comb;

    ///////////////////////////
    // Session configuration //
    ///////////////////////////
    // These configurations can be overwritten by a dynamic interface instance at runtime but are
    // fix for static interfaces.
    app_ses_config_t session_cfg;
  } app_config_t;

  parameter app_config_t AppCfgKeyMgr = '{
    if_type:       AppStatic,
    masked:        1'b0,
    // {fname: encoded_string("KMAC"), custom_str: encoded_string("")}
    prefix:        NSPrefixW'({EncodedStringEmpty, EncodedStringKMAC}),
    en_unsup_comb: 1'b0,
    session_cfg: '{
      prefix_mode: 1'b1,
      mode:        AppKMAC,
      kstrength:   sha3_pkg::L256,
      en_xof:      1'b0
    }
  };

  parameter app_config_t AppCfgLcCtrl= '{
    if_type:       AppStatic,
    masked:        1'b0,
    // {fname: encode_string(""), custom_str: encode_string("LC_CTRL")}
    prefix:        NSPrefixW'({EncodedStringLcCtrl, EncodedStringEmpty}),
    en_unsup_comb: 1'b0,
    session_cfg: '{
      prefix_mode: 1'b1,
      mode:        AppCShake,
      kstrength:   sha3_pkg::L128,
      en_xof:      1'b0
    }
  };

  parameter app_config_t AppCfgRomCtrl = '{
    if_type:       AppStatic,
    masked:        1'b0,
    // {fname: encode_string(""), custom_str: encode_string("ROM_CTRL")}
    prefix:        NSPrefixW'({EncodedStringRomCtrl, EncodedStringEmpty}),
    en_unsup_comb: 1'b0,
    session_cfg: '{
      prefix_mode: 1'b1,
      mode:        AppCShake,
      kstrength:   sha3_pkg::L256,
      en_xof:      1'b0
    }
  };

  parameter app_config_t AppCfgOtbn = '{
    if_type:       AppDynamic,
    masked:        1'b1,
    // Fixed "KMAC" prefix for KMAC operation.
    prefix:        NSPrefixW'({EncodedStringEmpty, EncodedStringKMAC}),
    en_unsup_comb: 1'b0,
    session_cfg: '{
      prefix_mode: 1'b0,
      mode:        AppShake,
      kstrength:   sha3_pkg::L256,
      en_xof:      1'b1
    }
  };

  // Exporting the app internal mux selection enum into the package. So that DV
  // can use this enum in its scoreboard.
  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 3 -m 4 -n 5 \
  //      -s 713832113 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||||||||| (66.67%)
  //  4: |||||||||| (33.33%)
  //  5: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 4
  // Minimum Hamming weight: 1
  // Maximum Hamming weight: 4
  //
  localparam int AppMuxWidth = 5;
  typedef enum logic [AppMuxWidth-1:0] {
    SelNone   = 5'b10100,
    SelApp    = 5'b11001,
    SelOutLen = 5'b00010,
    SelSw     = 5'b01111
  } app_mux_sel_e ;

  // Encoding generated at commit 77aa3fcc58 using Python 3.10.19 with:
  // $ ./util/design/sparse-fsm-encode.py --language=sv \
  //     --seed 3362063275 --distance 3 --states 18 --bits 10
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||| (13.07%)
  //  4: |||||||||||||||||||| (26.14%)
  //  5: ||||||||||||||||||| (24.84%)
  //  6: |||||||||||||| (18.30%)
  //  7: |||||||| (10.46%)
  //  8: |||| (5.23%)
  //  9: | (1.96%)
  // 10: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 9
  // Minimum Hamming weight: 3
  // Maximum Hamming weight: 7
  //
  localparam int AppStateWidth = 10;
  typedef enum logic [AppStateWidth-1:0] {
    StIdle = 10'b0110100101,

    // In StAppCfg state, it latches the cfg from AppCfg parameter to determine the kmac_mode,
    // sha3_mode, and keccak strength.
    // In StAppOutLen, the app interface pushes encoded output length into the core.
    StAppCfg        = 10'b1000001010,
    StAppMsg        = 10'b1011100000,
    StAppOutLen     = 10'b0011101110,
    StAppProcess    = 10'b0100111111,
    StAppWait       = 10'b0100010001,
    StAppPushDigest = 10'b1100100011,
    StAppFinish     = 10'b1001110010,

    // SW Controlled
    // If start request comes from SW first, until the operation ends, all
    // requests from apps will be stalled.
    StSw = 10'b1101000010,

    // Error KeyNotValid triggers if key is used but it is not valid at the time.
    StErrorKeyNotValid = 10'b0000001111,

    StErrorAwaitMsg         = 10'b1100100100,
    StErrorNotify           = 10'b0111100010,
    StErrorAwaitTermination = 10'b0101101000,
    StErrorFinish           = 10'b0011111101,
    StErrorAwaitSw          = 10'b0100001100,
    StErrorAwaitAbsorbed    = 10'b1110001111,
    StErrorPush             = 10'b0010110100,

    // This state is used for terminal errors
    StTerminalError = 10'b1101111001
  } st_e;

  // MsgWidth : 64
  // MsgStrbW : 8
  parameter int unsigned AppDigestW = 384;
  parameter int unsigned AppKeyW = 256;
  // Width of one digest chunk returned per rsp_valid pulse in AppDynamic mode.
  parameter int unsigned DynAppDigestW = MsgWidth;

  typedef struct packed {
    logic req_valid;
    logic [MsgWidth-1:0] data_s0;
    logic [MsgWidth-1:0] data_s1;
    logic [MsgStrbW-1:0] strb;
    logic req_last;
    logic rsp_ready;
  } app_req_t;

  typedef struct packed {
    logic req_ready;
    logic rsp_valid;
    logic [AppDigestW-1:0] digest_s0;
    logic [AppDigestW-1:0] digest_s1;
    // Error is valid when rsp_valid is high. If any error occurs during KDF, KMAC
    // returns the garbage digest data with error. The KeyMgr discards the
    // digest and may re-initiate the process.
    logic error;
    logic rsp_finish;
  } app_rsp_t;

  parameter app_req_t APP_REQ_DEFAULT = '{
    req_valid: 1'b0,
    data_s0:   '0,
    data_s1:   '0,
    strb:      '0,
    req_last:  1'b0,
    rsp_ready: 1'b0
  };

  parameter app_rsp_t APP_RSP_DEFAULT = '{
    req_ready:  1'b0,
    rsp_valid:  1'b0,
    digest_s0:  '0,
    digest_s1:  '0,
    error:      1'b0,
    rsp_finish: 1'b0
  };

  ////////////////////
  // Error Handling //
  ////////////////////

  // Error structure is same to the SHA3 one. The codes do not overlap.
  typedef enum logic [7:0] {
    ErrNone = 8'h 00,

    // ErrSha3SwControl occurs when software sent wrong flow signal.
    // e.g) Sw set `process_i` without `start_i`. The state machine ignores
    //      the signal and report through the error FIFO.
    //ErrSha3SwControl = 8'h 80

    // ErrKeyNotValid: KeyMgr interface raises an error if the secret key is
    // not valid when KeyMgr initiates KDF.
    ErrKeyNotValid = 8'h 01,

    // ErrSwPushMsgFifo: Sw writes data into Msg FIFO abruptly.
    // This error occurs in below scenario:
    //   - Sw does not send "Start" command to KMAC then writes data into
    //     Msg FIFO
    //   - Sw writes data into Msg FIFO when KeyMgr is in operation
    ErrSwPushedMsgFifo = 8'h 02,

    // ErrSwIssuedCmdInAppActive
    //  - Sw writes any command while AppIntf is in active.
    ErrSwIssuedCmdInAppActive = 8'h 03,

    // ErrWaitTimerExpired
    // Entropy Wait timer expired. Something wrong on EDN i/f
    ErrWaitTimerExpired = 8'h 04,

    // ErrIncorrectEntropyMode
    // Incorrect Entropy mode when entropy is ready
    ErrIncorrectEntropyMode = 8'h 05,

    // ErrUnexpectedModeStrength
    ErrUnexpectedModeStrength = 8'h 06,

    // ErrIncorrectFunctionName "KMAC"
    ErrIncorrectFunctionName = 8'h 07,

    // ErrSwCmdSequence
    ErrSwCmdSequence = 8'h 08,

    // ErrSwHashingWithoutEntropyReady
    //  - Sw issues KMAC op without Entropy setting.
    ErrSwHashingWithoutEntropyReady = 8'h 09,

    // Error due to lc_escalation_en_i or fatal fault
    ErrFatalError = 8'h C1,

    // Error due to the counter integrity check failure inside MsgFifo.Packer
    ErrPackerIntegrity = 8'h C2,

    // Error due to the counter integrity check failure inside MsgFifo.Fifo
    ErrMsgFifoIntegrity = 8'h C3
  } err_code_e;

  typedef struct packed {
    logic        valid;
    err_code_e   code; // Type of error
    logic [23:0] info; // Additional Debug info
  } err_t;
  parameter int unsigned ErrInfoW = 24 ; // err_t::info

  typedef struct packed {
    logic [AppDigestW-1:0] digest_share0;
    logic [AppDigestW-1:0] digest_share1;
  } rsp_digest_t;
  ///////////////////////
  // Library Functions //
  ///////////////////////

  // Endian conversion functions (32-bit, 64-bit)
  function automatic logic [31:0] conv_endian32( input logic [31:0] v, input logic swap);
    logic [31:0] conv_data;
    conv_data = {<<8{v}};
    conv_endian32 = (swap) ? conv_data : v ;
  endfunction : conv_endian32

endpackage : kmac_pkg
