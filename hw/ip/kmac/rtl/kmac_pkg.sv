// Copyright lowRISC contributors.
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
  parameter int unsigned EntropyLfsrW = 800;
  parameter int unsigned ChunkSizeEntropyLfsr = 32;
  parameter int unsigned NumChunksEntropyLfsr = EntropyLfsrW / ChunkSizeEntropyLfsr;

  // We use a single seed that is split down into chunks internally.
  // These LFSR parameters have been generated with
  // $ ./util/design/gen-lfsr-seed.py --width 800 --seed 3369807298 --prefix ""
  typedef logic [EntropyLfsrW-1:0] lfsr_seed_t;
  typedef logic [EntropyLfsrW-1:0][$clog2(EntropyLfsrW)-1:0] lfsr_perm_t;
  parameter lfsr_seed_t RndCnstLfsrSeedDefault = {
    32'h34a19ca3,
    256'he514d8e17a5630c287247dff3d354c022f581ace4b6c5736b5efa4160261ab0f,
    256'h6cb2915197ab3588982bcffc9cf3b46a250cebf728c0e76f0e680420d7f428f2,
    256'h092c1e308f7c8f9d8bacc20cd18fd586d58879654aa4851de224033bfdcbc578
  };
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
  // $ ./util/design/gen-lfsr-seed.py --width 32 --seed 2336700764 --prefix ""
  parameter int LfsrFwdWidth = 32;
  typedef logic [LfsrFwdWidth-1:0][$clog2(LfsrFwdWidth)-1:0] lfsr_fwd_perm_t;
  parameter lfsr_fwd_perm_t RndCnstLfsrFwdPermDefault = {
    160'h7f3ac6d173d78678d84908157fba482e76685704
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

  // Number of the application interface
  // Currently KMAC has three interface.
  // 0: KeyMgr
  // 1: LC_CTRL
  // 2: ROM_CTRL
  // Make sure to change `width` of app inter-module signal definition
  // if this value is changed.
  parameter int unsigned NumAppIntf = 3;

  // Application Algorithm
  // Each interface can choose algorithms among SHA3, cSHAKE, KMAC
  typedef enum bit [1:0] {
    // SHA3 mode doer not nees any additional information.
    // Prefix will be tied to all zero and not used.
    AppSHA3   = 0,

    // In CShake/ KMAC mode, the Prefix can be determined by the compile-time
    // parameter or through CSRs.
    AppCShake = 1,

    // In KMAC mode, the secret key always comes from sideload.
    // KMAC mode needs uniformly distributed entropy. The request will be
    // silently discarded in Reset state.
    AppKMAC   = 2
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
    app_mode_e Mode;

    sha3_pkg::keccak_strength_e Strength;

    // PrefixMode determines the origin value of Prefix that is used in KMAC
    // and cSHAKE operations.
    // Choose **0** for CSRs (!!PREFIX), or **1** to use `Prefix` parameter
    // below.
    bit PrefixMode;

    // If `PrefixMode` is 1'b 1, then this `Prefix` value will be used in
    // cSHAKE or KMAC operation.
    logic [NSPrefixW-1:0] Prefix;
  } app_config_t;

  parameter app_config_t AppCfg [NumAppIntf] = '{
    // KeyMgr
    '{
      Mode:       AppKMAC, // KeyMgr uses KMAC operation
      Strength:   sha3_pkg::L256,
      PrefixMode: 1'b 1,   // Use prefix parameter
      // {fname: encoded_string("KMAC"), custom_str: encoded_string("")}
      Prefix:     NSPrefixW'({EncodedStringEmpty, EncodedStringKMAC})
    },

    // LC_CTRL
    '{
      Mode:       AppCShake,
      Strength:   sha3_pkg::L128,
      PrefixMode: 1'b 1,     // Use prefix parameter
      // {fname: encode_string(""), custom_str: encode_string("LC_CTRL")}
      Prefix: NSPrefixW'({EncodedStringLcCtrl, EncodedStringEmpty})
    },

    // ROM_CTRL
    '{
      Mode:       AppCShake,
      Strength:   sha3_pkg::L256,
      PrefixMode: 1'b 1,     // Use prefix parameter
      // {fname: encode_string(""), custom_str: encode_string("ROM_CTRL")}
      Prefix: NSPrefixW'({EncodedStringRomCtrl, EncodedStringEmpty})
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



  // MsgWidth : 64
  // MsgStrbW : 8
  parameter int unsigned AppDigestW = 384;
  parameter int unsigned AppKeyW = 256;

  typedef struct packed {
    logic valid;
    logic [MsgWidth-1:0] data;
    logic [MsgStrbW-1:0] strb;
    logic last;
  } app_req_t;

  typedef struct packed {
    logic ready;
    logic done;
    logic [AppDigestW-1:0] digest_share0;
    logic [AppDigestW-1:0] digest_share1;
    // Error is valid when done is high. If any error occurs during KDF, KMAC
    // returns the garbage digest data with error. The KeyMgr discards the
    // digest and may re-initiate the process.
    logic error;
  } app_rsp_t;

  parameter app_req_t APP_REQ_DEFAULT = '{
    valid: 1'b 0,
    data: '0,
    strb: '0,
    last: 1'b 0
  };
  parameter app_rsp_t APP_RSP_DEFAULT = '{
    ready: 1'b1,
    done:  1'b1,
    digest_share0: AppDigestW'(32'hDEADBEEF),
    digest_share1: AppDigestW'(32'hFACEBEEF),
    error: 1'b1
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

    // Error Shadow register update
    ErrShadowRegUpdate = 8'h C0,

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
    logic [31:0] conv_data = {<<8{v}};
    conv_endian32 = (swap) ? conv_data : v ;
  endfunction : conv_endian32

  function automatic logic [63:0] conv_endian64( input logic [63:0] v, input logic swap);
    logic [63:0] conv_data = {<<8{v}};
    conv_endian64 = (swap) ? conv_data : v ;
  endfunction : conv_endian64

endpackage : kmac_pkg
