// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// sha3_pkg

package sha3_pkg;

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

  // SHA3 core state. This state value is used in sha3core module
  // and also in KMAC top module and the register interface for sw to track the
  // sha3 status.
  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 3 -m 7 -n 6 \
  //      -s 4082450958 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||||||||| (57.14%)
  //  4: ||||||||||||||| (42.86%)
  //  5: --
  //  6: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 4
  // Minimum Hamming weight: 1
  // Maximum Hamming weight: 4
  //
  localparam int StateWidth = 6;
  typedef enum logic [StateWidth-1:0] {
    StIdle_sparse = 6'b101100,

    // Absorb stage receives the message bitstream and computes the keccak
    // rounds. This internal operation is mainly done inside sha3pad module
    // not sha3core. The core module and this state machine observe the status
    // of the process and mainly waits until all the sponge absorbing is
    // completed. The main indicator is `absorbed` signal.
    StAbsorb_sparse = 6'b100001,

    // TODO: Implement StAbort later after context-switching discussion.
    // Abort stage can be moved from StAbsorb stage. It basically holds the
    // keccak round operation and opens up the internal state variable to the
    // software. This stage is for the software to pause current operation and
    // store the internal state elsewhere then initiates new KMAC/SHA3 process.
    // StAbort only can be moved to _StFlush_.
    //StAbort_sparse = 6'b011101,

    // Squeeze stage allows the software to read the internal state.
    // If `EnMasking`, it opens the read permission of two share of the state.
    // The squeezing in SHA3 specification describes the software to read up to
    // the rate of SHA3 algorithm but this logic opens up the entire 1600 bits
    // of the state (3200bits if `EnMasking`).
    StSqueeze_sparse = 6'b001011,

    // ManualRun stage initiaties the keccak round and waits the completion.
    // This state is moved from Squeeze state by writing 1 to manual_run CSR.
    // When keccak round is completed, it goes back to Squeeze state.
    StManualRun_sparse = 6'b010000,

    // Flush stage, the core clears out the internal variables and also
    // submodules' variables too. Then moves back to Idle state.
    StFlush_sparse =  6'b000110,

    StTerminalError_sparse = 6'b111010
  } sha3_st_sparse_e;

  localparam int StateWidthLogic = 3;
  typedef enum logic [StateWidthLogic-1:0] {
    StIdle,
    StAbsorb,
    //StAbort,
    StSqueeze,
    StManualRun,
    StFlush,
    StError
  } sha3_st_e;

  function automatic sha3_st_e sparse2logic(sha3_st_sparse_e st);
    unique case (st)
      StIdle_sparse      : return StIdle;
      StAbsorb_sparse    : return StAbsorb;
      //StAbort_sparse   : return StAbort;
      StSqueeze_sparse   : return StSqueeze;
      StManualRun_sparse : return StManualRun;
      StFlush_sparse     : return StFlush;
      default            : return StError;
    endcase
  endfunction : sparse2logic

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


  ///////////////
  // Functions //
  ///////////////

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


endpackage : sha3_pkg
