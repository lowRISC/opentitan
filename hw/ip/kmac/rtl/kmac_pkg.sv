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

  parameter int KeccakRate [5] = '{
    1344/MsgWidth,  // 21 depth := (1600 - 128*2)
    1152/MsgWidth,  // 18 depth := (1600 - 224*2)
    1088/MsgWidth,  // 17 depth := (1600 - 256*2)
     832/MsgWidth,  // 13 depth := (1600 - 384*2)
     576/MsgWidth   //  9 depth := (1600 - 512*2)
  };

  parameter int MaxBlockSize = KeccakRate[0];

  parameter int KeccakEntries = 1600/MsgWidth;
  parameter int KeccakMsgAddrW = $clog2(KeccakEntries);

  parameter int KeccakCountW = $clog2(KeccakEntries+1);

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

endpackage : kmac_pkg
