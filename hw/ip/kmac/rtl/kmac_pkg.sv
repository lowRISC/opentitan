// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// kmac_pkg

package kmac_pkg;

  // StateW represents the width of Keccak state variable.
  // As Sha3 assume the state value as 1600, this shouldn't be modified.
  // Note that keccak_round is flexible. It can have any values defined in SHA3
  // specification. But sha3pad logic assumes the value as 1600.
  parameter int StateW = 1600;

  // Function Name (N) and Customzation String (S) shall be
  // smaller than 2**256 bits and integer divisiable by 8.
  parameter int FnWidth = 32;  // up to 32bit Function Name
  parameter int CsWidth = 256; // up to 256bit Customization Input

  // Calculate left_encode(len( X )) bit size.
  // Assume the enc_8(n) is always 1 (up to 255 byte of len(S) size)
  // e.g) 248bit --> two bytes , 256bit --> three bytes
  //  round8bit(clog2(X+1))/8

  parameter int MaxFnEncodeSize = ($clog2(FnWidth+1) + 8 - 1) / 8 + 1;
  parameter int MaxCsEncodeSize = ($clog2(CsWidth+1) + 8 - 1) / 8 + 1;

  parameter int NSRegisterSizePre = FnWidth/8       + CsWidth/8
                                  + MaxFnEncodeSize + MaxCsEncodeSize;
  // Round up to 32bit word base
  parameter int NSRegisterSize = ((NSRegisterSizePre + 4 - 1 ) / 4) * 4;

  // Prefix represents bytepad(encode_string(N) || encode_string(S), 168 or 136)
  // +2 represents left_encoding(168 or 136) which could be either:
  // 10000000 || 00010101 // 168
  // 10000000 || 00010001 // 136
  parameter int PrefixSize = NSRegisterSize + 2;

  // index width for `N` and `S`
  parameter int PrefixIndexW = $clog2(PrefixSize/64);

  // Datapath width in KMAC, this also affects the output of MSG_FIFO
  // This is assumed as 64 in KMAC design. If this value is changed, some parts
  // of the KMAC design need to be changed.
  //
  // 1. keccak_round logic datapath. Keccak round logic assumes MsgWidth
  //    divides 1600 keccak state `Width`. Choose the value accordingly.
  // 2. sha3pad module has fixed width mux for funcpad logic. If MsgWidth is
  //    changed, the logic also need to be revised.
  // 3. kmac core logic also has fixed size mux for appeding output length.
  //    Revise the case statement to fit into revised MsgWidth value.
  parameter int MsgWidth = 64;
  parameter int MsgStrbW = MsgWidth / 8;

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

  // Keccak module supports SHA3, SHAKE, cSHAKE function.
  // This mode determines if the module uses encoded N and S or not.
  // Also it chooses the padding value.
  //
  //    mode   |  little-endian
  //    -------|----------------
  //    Sha3   |  2'b   10
  //    Shake  |  4'b 1111
  //    CShake |  2'b   00
  //
  // Please remind that if input strings N and S are empty, SW shall
  // choose SHAKE even for cSHAKE operation.
  typedef enum logic[1:0] {
    Sha3   = 2'b 00,
    Shake  = 2'b 10,
    CShake = 2'b 11
  } sha3_mode_e;

  // keccak_strength_e determines the security strength against collision attack
  // This value decides the _rate_ and _capacity_ of the keccak states.
  // It affects the sha3pad module too. the padding module implements
  // `bytepad(X,168)` for L128, `bytepad(X,136)` for L256 in cSHAKE
  typedef enum logic [2:0] {
    L128 = 3'b 000, // rate: 1344 bit / capacity:  256 bit Keccak[ 256](, 128)
    L224 = 3'b 001, // rate: 1152 bit / capacity:  448 bit Keccak[ 448](, 224)
    L256 = 3'b 010, // rate: 1088 bit / capacity:  512 bit Keccak[ 512](, 256)
    L384 = 3'b 011, // rate:  832 bit / capacity:  768 bit Keccak[ 768](, 384)
    L512 = 3'b 100  // rate:  576 bit / capacity: 1024 bit Keccak[1024](, 512)
  } keccak_strength_e;

  parameter int unsigned KeccakRate [5] = '{
    1344/MsgWidth,  // 21 depth := (1600 - 128*2)
    1152/MsgWidth,  // 18 depth := (1600 - 224*2)
    1088/MsgWidth,  // 17 depth := (1600 - 256*2)
     832/MsgWidth,  // 13 depth := (1600 - 384*2)
     576/MsgWidth   //  9 depth := (1600 - 512*2)
  };

  parameter int unsigned MaxBlockSize = KeccakRate[0];

  parameter int unsigned KeccakEntries = 1600/MsgWidth;
  parameter int unsigned KeccakMsgAddrW = $clog2(KeccakEntries);

  parameter int unsigned KeccakCountW = $clog2(KeccakEntries+1);

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


  // SHA3 core state. This state value is used in sha3core module
  // and also in KMAC top module and the register interface for sw to track the
  // sha3 status.
  typedef enum logic [2:0] {
    StIdle,

    // Absorb stage receives the message bitstream and computes the keccak
    // rounds. This internal operation is mainly done inside sha3pad module
    // not sha3core. The core module and this state machine observe the status
    // of the process and mainly waits until all the sponge absorbing is
    // completed. The main indicator is `absorbed` signal.
    StAbsorb,

    // TODO: Implement StAbort later after context-switching discussion.
    // Abort stage can be moved from StAbsorb stage. It basically holds the
    // keccak round operation and opens up the internal state variable to the
    // software. This stage is for the software to pause current operation and
    // store the internal state elsewhere then initiates new KMAC/SHA3 process.
    // StAbort only can be moved to _StFlush_.
    //StAbort,

    // Squeeze stage allows the software to read the internal state.
    // If `EnMasking`, it opens the read permission of two share of the state.
    // The squeezing in SHA3 specification describes the software to read up to
    // the rate of SHA3 algorithm but this logic opens up the entire 1600 bits
    // of the state (3200bits if `EnMasking`).
    StSqueeze,

    // ManualRun stage initiaties the keccak round and waits the completion.
    // This state is moved from Squeeze state by writing 1 to manual_run CSR.
    // When keccak round is completed, it goes back to Squeeze state.
    StManualRun,

    // Flush stage, the core clears out the internal variables and also
    // submodules' variables too. Then moves back to Idle state.
    StFlush
  } sha3_st_e;

  // kmac_cmd_e defines the possible command sets that software issues via
  // !!CMD register. This is mainly to limit the error scenario that SW writes
  // multiple commands at once.
  typedef enum logic [3:0] {
    CmdStart     = 4'b 0001,
    CmdProcess   = 4'b 0010,
    CmdManualRun = 4'b 0100,
    CmdDone      = 4'b 1000
  } kmac_cmd_e;

  //////////////////
  // Error Report //
  //////////////////
  typedef enum logic [7:0] {
    ErrNone = 8'h 00,

    // ErrSha3SwControl occurs when software sent wrong flow signal.
    // e.g) Sw set `process_i` without `start_i`. The state machine ignores
    //      the signal and report through the error FIFO.
    ErrSha3SwControl = 8'h 80
  } err_code_e;

  typedef struct packed {
    logic        valid;
    err_code_e   code; // Type of error
    logic [23:0] info; // Additional Debug info
  } err_t;


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

  // Bytepading function
  // `encode_bytepad_len` represents the first two bytes of bytepad()
  // It depends on the block size. We can reuse KeccakRate
  // 10000000 || 00010101 // 168
  // 10000000 || 00010001 // 136
  function automatic logic [15:0] encode_bytepad_len(keccak_strength_e kstrength);
    logic [15:0] result;
    unique case (kstrength)
      L128: result = 16'h A801; // cSHAKE128
      L224: result = 16'h 9001; // not used
      L256: result = 16'h 8801; // cSHAKE256
      L384: result = 16'h 6801; // not used
      L512: result = 16'h 4801; // not used

      default: result = 16'h 0000;
    endcase
    return result;
  endfunction : encode_bytepad_len

endpackage : kmac_pkg
