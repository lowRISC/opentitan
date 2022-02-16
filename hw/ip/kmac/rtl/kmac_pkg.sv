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
  // multiple commands at once.
  typedef enum logic [3:0] {
    CmdNone      = 4'b 0000,
    CmdStart     = 4'b 0001,
    CmdProcess   = 4'b 0010,
    CmdManualRun = 4'b 0100,
    CmdDone      = 4'b 1000
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

  // entropy lfsr related
  parameter int unsigned EntropyLfsrW = 64;
  typedef logic [EntropyLfsrW-1:0] lfsr_seed_t;
  typedef logic [EntropyLfsrW-1:0][$clog2(EntropyLfsrW)-1:0] lfsr_perm_t;
  parameter lfsr_seed_t RndCnstLfsrSeedDefault = 64'h47e808241ebaa563;
  parameter lfsr_perm_t RndCnstLfsrPermDefault = {
    128'hc4ffd50080c2bba9a263211ef56f8d4b,
    256'h9da89ed97481a32c5d9a4650abeb9388fcedcab36df411849df5c057473812d3
  };

  // These LFSR parameters have been generated with
  // $ ./util/design/gen-lfsr-seed.py --width 64 --seed 1201202158 --prefix ""
  // And changed the type name from lfsr_perm_t to msg_perm_t
  typedef logic [EntropyLfsrW-1:0][$clog2(EntropyLfsrW)-1:0] msg_perm_t;
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
    AppKMAC   = 2
  } app_mode_e;

  // Predefined encoded_string
  parameter logic [15:0] EncodedStringEmpty = 16'h 0001;
  parameter logic [47:0] EncodedStringKMAC = 48'h 4341_4D4B_2001;
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
      PrefixMode: 1'b 0,   // Use CSR for prefix
      Prefix:     '0       // Not used in CSR prefix mode
    },

    // LC_CTRL
    '{
      Mode:       AppCShake,
      Strength:   sha3_pkg::L128,
      PrefixMode: 1'b 1,     // Use prefix parameter
      // {fname: encode_string(""), custom_str: encode_string("LC_CTRL")}
      Prefix: NSPrefixW'(88'h 4c_5254_435f_434C_3801_0001)
    },

    // ROM_CTRL
    '{
      Mode:       AppCShake,
      Strength:   sha3_pkg::L256,
      PrefixMode: 1'b 1,     // Use prefix parameter
      // {fname: encode_string(""), custom_str: encode_string("ROM_CTRL")}
      Prefix: NSPrefixW'(96'h 4c52_5443_5f4d_4f52_4001_0001)
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
    // last indicates the last beat of the data. strb can be partial only with
    // last.
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

    // Error Shadow register update
    ErrShadowRegUpdate = 8'h C0,

    // Error due to lc_escalation_en_i or fatal fault
    ErrFatalError = 8'h C1
  } err_code_e;

  typedef struct packed {
    logic        valid;
    err_code_e   code; // Type of error
    logic [23:0] info; // Additional Debug info
  } err_t;

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

  // 5x 320-bit => 1600-bit shuffling parameters
  // These LFSR parameters have been generated with
  // $ ./util/design/gen-lfsr-seed.py --width 1600 --seed 2194103998 --prefix "storage"
  parameter int StoragePermWidth = 1600;
  typedef logic [StoragePermWidth-1:0][$clog2(StoragePermWidth)-1:0] storage_perm_t;
  parameter storage_perm_t RndCnstStoragePermDefault = {
    192'h9462bcd1b2e8253de545d548a414042651078dd41e287a70,
    256'h452b1d178740269d282cb4393c93eb6f7ff0980c6f4da49b0d0bd8076778ccc0,
    256'h04f13023232b410e2cdd9ce25a6f48724076a5b822b329c45a5410d48b99de34,
    256'hc7850e7297d5dc881fb0ce674e30aa339be49cb12ccc80aae96b4549748686e1,
    256'h5eabf53401e1a3b8cacb7e31a80e01201568a21449ad02c47451a1c5742e2b0c,
    256'h718527498819bac3836a6391447c6c2962554489356709a6a22885659b092028,
    256'h0f18ea0ac55c5b48282ec36ca99d952ca8c534973a2cb0682d538fead54ac10c,
    256'h73c0dbcb600d160d09db1aae2e58ed7482ba72558101270082b676adb0de0f16,
    256'h53645453fd9967f175277638f5a9832222a299895a67e5616e694b082b1a80a4,
    256'hebed65da38a95bee2adb3d97470186fc6c6d717274e189b15d9578b134aa312d,
    256'h1e00c3154808754123e88b088a8e7ed5382a5f882d033c7b567d8b02ce6df478,
    256'h5db7b0628b2dc3554e90c11ae3213ef891d2cf5fc5aa555563e2bada947106d8,
    256'h06270ebaf6348015d82253f2cf40a880835644538650ba9911d2484d19c38e68,
    256'h4dc5d99456e7342c80f30c4986f3315408e159ab9437ade00396e342755b239c,
    256'hadf75c43de283d305b0c5667a1d252c363e0a053d2dcc0ae2064cf0846130bd8,
    256'h3d792905d50c02929d9bac01156d8dd4197216321cc93923758091c85a405722,
    256'hd1d97e14cd5ea843faa60d9503bd018294d723b74a8eb5d936305b062e805c06,
    256'h6da9c236d8aa340a18be3b992b2f641219fc05ebe256a3c4522c882159205a48,
    256'h38112ad3aa37f6e2bb427eaa188492b7d74c7325e932118e657a648cc696c8f6,
    256'h60391795afc7070d79d6c4cc1ce8e4b366533d8a196c382f221c79108c6c9daf,
    256'hb1fd3596aab55ce72c633e6077485fc8350a91ea3700b44ce35f21214ce16d41,
    256'h58b2bb6382c5a3c06a3c668680e2f7c45d6d6ad3e0cf9e2804bc23de397bc870,
    256'h51550bc167cbc3406ef0715f5eb77f824c857192ac858eae0a46e0af50283a68,
    256'h628acd46a8bf50994c5d22d5c8b7f47a724ddd0f917686fe27b374784cf2d4c7,
    256'h73b97ab1e0418b8078aa7d7692444dc5cad39ca9dfb389548f31169585c6ea16,
    256'h544eaefd346b1e808f29d254658c9289591269c955269f2a7a4fab4716a1c73d,
    256'h3588a2a239cf200d24499cdf14f5cdb91cabc81704d9f298552713038a68b429,
    256'hb616760c8f1a82b44577e2532c5bb7bc6cbd16b66a21a9bea30ca0a9cae2e874,
    256'h20c1f50f1432ed4bb0b2229874ff98b5d1ee090b9124d39adb07c7b29fa58c2b,
    256'h7e13681162d49caccca99aa346b030b644c8474f51f3284ec0d121d380332503,
    256'h723a6e6368afa6b6539acc7aa2c7963abdd0fd4050761355f14938bf70e98c58,
    256'h030773ee49fe8d3528d5da00131415e60a0ca1a4882d7b7ea242385f51d31ea9,
    256'h54f5b49aa55bd55298c03d39e9fa306cc130bcad88a41af2d37790636008af02,
    256'h7d3dd12f2790a63352c3f288242b872c62f2342d6138f31a236f45dfdceb5481,
    256'h2847c072d8b0a1edb056761e4c1b57951f19bc25892509d360624cfb82ec2711,
    256'ha9f4b40cf3ee15c6bb50970444028f51f0a54380d498007e1026e6880d2ca0a5,
    256'h35495e8d5f91ed230941ea1e90cc4926c4de8cde0dd25a2ab4afd1d76cb8c568,
    256'he59af566ee4035d8eca57bbe8b638942e11b0d7a53e2a6128cf96093db18874a,
    256'h301aa6e8ae8d891acb3a077c643f043295b4d7d892da8e24b757d6fa376542c4,
    256'hcc4ddb3175550adc088d426622bf84cc1b07c2d31a7228501789a18cffb6748d,
    256'h59836d754b33990029a8fca191b3f5326f94658779b6059b33836bc149219411,
    256'hd08bdf0a4d4d71bc4662092c19148ae488e5b5d0c090748c286c34c5b27632ac,
    256'hd9da9a0cd49b5590b2fb842463002243195f4ee9b6b7475aa661bb01634f5dad,
    256'h43b2fd6965863ea8abb63ed820d92d99a4fe328b32383050656c63100104a8b4,
    256'hdfc2926237a27b032e24dc8400e25a5c9b2d7e778034780fb0d744ed42ae69eb,
    256'h0107ac5c58121713ffbe00a5145d618e8293c33f454660e39b38722c1c4c0804,
    256'h3180f7212b09322d98d83184ae47483829876ff2e12b6e6c3fda7058e49fe44c,
    256'hc3c19c5fc4224ef0824cf6bba5381c94dad74ba7559a8216f08157f5a45408a4,
    256'hf36aec1ee1247af23dcb3b040ec8f2353c6498101d3e2139a0994dbf38495a41,
    256'he07ca16681d01de30307d3204b832806f9c977a4fb50fe0b6e0866d6d675e956,
    256'h80f10d20950de297069097089e08a2c2cd072c92ed6b809a3e1d894e64af12c5,
    256'h5dc1fd088c292606d61422a7ef6ce20fcfa9653b721ed76d13cdc21604051553,
    256'hce16a590c4520950c8e198432015535fa72ec52d8795603f4d739f25f6d15dd3,
    256'hec6c07261c7487898e7a0129a55217794fad15b92ea3b38cb659b2708b30e297,
    256'hbda6a6e5ee542f368b79c83d88cf7384287d914aadc7cb42f4f6c69d06604e1e,
    256'h0da1eb1497d49de7a4a86c6185597ed70222a025910552c3173586e9eaa98c70,
    256'h31bcd4e978ccca3cce0dceec4c9516b2c99c0c1d44784b1f9187d0618f6c0e19,
    256'h45dccdca609a38c521524a2df66cbd42fe7a158c0faa783aa23af9342ddfa3ef,
    256'h06e226330049c6e8a89229510fdddedbb9025d54ee0256f2e62c0bd6d4890518,
    256'h9a3f52f97c5643891d66d01591b2123f9d76dc14cea4b58db8ac5d06f2328fc3,
    256'hdbe98ed813111a97cf01291227a74ff8ccd2c10241c27d6aa98790a0188b0684,
    256'h05c5c73ba08d294158554ecc22ff7c1785cc5c6c4ebde8fbc8a8d6f6c437cba2,
    256'h4294b91a8d610d1b9804d2f1083072888d630fa031c33ef039a46fc93e68d701,
    256'h3d6595cb412005ccc91b88ef3c4c141325cc2c000ffaf98bde79f43e78504102,
    256'h4b5964ec9542a7108a521ce9d978ee0d5cb1358d495b92135899e3962cc7e5dc,
    256'hc3e5ecf329882f1b640ee84a0490e106d0144714f1a63ce928fc5d2c4b338316,
    256'h8c893b3ab0de83ae5b0b980c1c064f56d96dc422f0a18b9617709fd8442bba81,
    256'h418f8d52b0d2e56a753d34151cb862447acbca7e2f863d8792930ebe65ec0b13,
    256'h82f9c9c5d1735e2a5ca23de262aea072949288e4c661966c613a923f57963827
  };
endpackage : kmac_pkg
