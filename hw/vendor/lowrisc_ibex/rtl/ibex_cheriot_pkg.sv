// Copyright lowRISC contributors.
// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// CHERIoT types, constants, and functions shared across Ibex.

package ibex_cheriot_pkg;

  // Capability width parameters (spec v1.0, chapter 7.13)
  //
  //                       31 30       25 24   22 21  18 17             9 8              0
  // +-----------+       +---+-----------+-------+------+----------------+----------------+
  // | valid tag |       | R |  cperms   | otype | cexp |    top (T)     |    base (B)    |
  // +-----------+       +---+-----------+-------+------+----------------+----------------+
  //      [1]             [1]      [6]      [3]    [4]         [9]               [9]
  //
  // Naming convention: C* prefix for compressed/stored form. No prefix for the expanded/working
  // form only used inside the core
  parameter int unsigned ADDR_W    = 32;
  parameter int unsigned CBOUND_W  = 9;   // 9-bit compressed bound (T or B)
  parameter int unsigned CEXP_W    = 4;   // 4-bit compressed exponent
  parameter int unsigned EXP_W     = 5;   // 5-bit expanded exponent
  parameter int unsigned OTYPE_W   = 3;   // 3-bit object type (sealing)
  parameter int unsigned CPERMS_W  = 6;   // 6-bit compressed permissions
  parameter int unsigned PERMS_W   = 12;  // 12-bit expanded permissions
  // Width of the compressed capability type (cap_t) as a flat vector used for ECC protection.
  parameter int unsigned REGCAP_W = 35;

  // Capability typedefs
  typedef logic [CBOUND_W-1:0] cbound_t;  // 9-bit compressed bound (T or B)
  typedef logic [CEXP_W-1:0]   cexp_t;    // 4-bit compressed exponent
  typedef logic [EXP_W-1:0]    exp_t;     // 5-bit expanded exponent
  typedef logic [OTYPE_W-1:0]  otype_t;   // 3-bit object type (sealing)
  typedef logic [CPERMS_W-1:0] cperms_t;  // 6-bit compressed permissions
  typedef logic [1:0]          cap_cor_t; // 2-bit correction: [1]=top_hi^addr_hi, [0]=addr_hi

  // Expanded 12-bit permissions (spec v1.0, chapter 7.13.1)
  typedef struct packed {
    logic U0;  // [11] user permission (software-defined)
    logic SE;  // [10] seal
    logic US;  // [9]  unseal
    logic EX;  // [8]  execute
    logic SR;  // [7]  access system registers
    logic MC;  // [6]  load/store capability
    logic LD;  // [5]  load
    logic SL;  // [4]  store local capability
    logic LM;  // [3]  load mutable
    logic SD;  // [2]  store
    logic LG;  // [1]  load global
    logic GL;  // [0]  global
  } perms_t;

  // Sealing types (spec v1.0, chapter 7.13.2)
  parameter otype_t OTYPE_UNSEALED        = 3'd0; // unsealed
  parameter otype_t OTYPE_SENTRY_II_FWD   = 3'd1; // interrupt-inheriting forward sentry
  parameter otype_t OTYPE_SENTRY_ID_FWD   = 3'd2; // interrupt disabling forward sentry
  parameter otype_t OTYPE_SENTRY_IE_FWD   = 3'd3; // interrupt enabling forward sentry
  parameter otype_t OTYPE_SENTRY_ID_BKWD  = 3'd4; // interrupt disabling backward sentry
  parameter otype_t OTYPE_SENTRY_IE_BKWD  = 3'd5; // interrupt enabling backward sentry

  // Exponent (spec v1.0, chapter 7.13.3)
  parameter cexp_t MAXCEXP = 4'd15; // compressed maximum exponent encoding
  parameter exp_t  MAXEXP  = 5'd24; // expanded maximum exponent

  // -----------------------------------------------------------------------------------------------
  // Capability types
  // -----------------------------------------------------------------------------------------------
  // The CHERIoT ISA defines the capability format (spec v1.0, chapter 7.13, Figure 7.2).
  // Two types are used in the RTL:
  //
  //  cap_t          - The primary compressed form defined by the spec and used everywhere a
  //                   capability is stored (register file, CSR registers, load/store ports,
  //                   ECC/lockstep vectors). Its lower 33 bits (cap[32:0]) are a 1:1 match with the
  //                   spec so writing to memory is a simple truncation and a direct cast.
  //                   Bits [34:33] store the correction factors that are not in the spec but kept
  //                   in the register file to save recomputation costs. See the
  //                   `cheriot_compute_corrections` function below.
  //
  //  decoded_cap_t  - The uncompressed capability type used inside the core. Created by
  //                   `cheriot_decode_cap` and `cheriot_encode_cap`. Its lower 35 bits are the same
  //                   as cap_t so encode is simpley a cast. The upper bits add the decompressed
  //                   bounds and permissions.
  // -----------------------------------------------------------------------------------------------

  // Compressed capability + correction factors
  typedef struct packed {
    cap_cor_t cap_cor; // [34:33] correction factors
    // Capability according to spec v1.0, chapter 7.13
    logic     valid;   // [32]    tag bit
    logic     rsvd;    // [31]    reserved R
    cperms_t  cperms;  // [30:25] compressed permissions
    otype_t   otype;   // [24:22] object type
    cexp_t    cexp;    // [21:18] 4-bit compressed exponent
    cbound_t  top;     // [17:9]  top mantissa T
    cbound_t  base;    // [8:0]   base mantissa B
  } cap_t;  // 2+1+1+6+3+4+9+9 = 35 bits = REGCAP_W

  // Uncompressed capability
  typedef struct packed {
    logic [ADDR_W:0]   top33;  // 33 bits absolute top
    logic [ADDR_W-1:0] base32; // 32 bits absolute base
    perms_t            perms;  // 12 bits expanded permissions
    // Identical layout to cap_t from here
    cap_cor_t cap_cor; // [34:33] correction factors
    logic     valid;   // [32]    tag bit
    logic     rsvd;    // [31]    reserved R
    cperms_t  cperms;  // [30:25] compressed permissions
    otype_t   otype;   // [24:22] object type
    cexp_t    cexp;    // [21:18] 4-bit compressed exponent
    cbound_t  top;     // [17:9]  top mantissa T
    cbound_t  base;    // [8:0]   base mantissa B
  } decoded_cap_t;  // 33+32+12+35 = 112 bits


  // Types for bound computation in CHERIoT EX Stage
  typedef struct packed {
    logic [32:0]    top33req; // requested top = addr + length (33-bit)
    exp_t           exp1;     // exponent candidate from length (no overflow)
    exp_t           exp2;     // exp1 + 1 (used when exp1 path overflows)
    logic [EXP_W:0] explen;   // MSB position of length[31:9] (6-bit, can be 32)
    logic [EXP_W:0] expb;     // trailing-zero count of base address (6-bit)
    logic           in_bound; // addr..addr+length lies within parent bounds
  } bound_req_t;

  // The decoded capability plus the alignment mask and representable length.
  typedef struct packed {
    decoded_cap_t cap;   // resulting capability
    logic [31:0]  maska; // alignment mask    (CRAM result)
    logic [31:0]  rlen;  // representable len (CRRL result)
  } bound_result_t;

  // Permission-clearing control for capability loads (CLC instruction).
  // Each field corresponds to one CLC clearing rule from the spec.
  typedef struct packed {
    logic CTAG;   // [2] clear tag (valid) bit (loading cap lacks MC)
    logic SD_LM;  // [1] clear SD and LM       (loading cap lacks LM)
    logic GL_LG;  // [0] clear GL and LG       (loading cap lacks LG)
  } cap_clrperm_t;

  // -----------------------------------------------------------------------------------------------
  // Root Capabilities and Constants
  // -----------------------------------------------------------------------------------------------
  parameter cap_t         NULL_CAP         = '{default: '0};
  parameter decoded_cap_t NULL_DECODED_CAP = '{default: '0};

  // Three CHERIoT root capabilities (spec v1.0, chapter 7.13.1)
  parameter logic [5:0] CPERMS_TX = 6'b101111;  // Tx (executable root)
  parameter logic [5:0] CPERMS_TM = 6'b111111;  // Tm (memory root)
  parameter logic [5:0] CPERMS_TS = 6'b100111;  // Tx (sealing root)

  // ROOT_DECODED_CAP_TX is used for the PCC. All other root capabilities are cap_t
  // Executable Root Capability
  parameter decoded_cap_t ROOT_DECODED_CAP_TX = '{
    top33:   33'h10000_0000,
    base32:  '0,
    perms:   12'h1eb,
    cap_cor: '0,
    valid:   1'b1,
    rsvd:    1'b0,
    cperms:  CPERMS_TX,
    otype:   OTYPE_UNSEALED,
    cexp:    MAXCEXP,
    top:     9'h100,
    base:    '0
  };
  parameter cap_t ROOT_CAP_TX = cap_t'(ROOT_DECODED_CAP_TX);

  // Memory Root Capability
  parameter cap_t ROOT_CAP_TM = '{
    cap_cor: '0,
    valid:   1'b1,
    rsvd:    1'b0,
    cperms:  CPERMS_TM,
    otype:   OTYPE_UNSEALED,
    cexp:    MAXCEXP,
    top:     9'h100,
    base:    '0
  };

  // Sealing Root Capability
  parameter cap_t ROOT_CAP_TS = '{
    cap_cor: '0,
    valid:   1'b1,
    rsvd:    1'b0,
    cperms:  CPERMS_TS,
    otype:   OTYPE_UNSEALED,
    cexp:    MAXCEXP,
    top:     9'h100,
    base:    '0
  };


  // Implicit permission masks for each compressed permission format (spec v1.0, chapter 7.13.1)
  parameter perms_t PERM_MRW_IMSK = '{LD:1, MC:1, SD:1, default:0}; // Memory cap-read-write
  parameter perms_t PERM_MRO_IMSK = '{LD:1, MC:1, default:0};       // Memory cap-read-only
  parameter perms_t PERM_MWO_IMSK = '{SD:1, MC:1, default:0};       // Memory cap-write-only
  parameter perms_t PERM_MDO_IMSK = '{default:0};                   // Memory data-only
  parameter perms_t PERM_EXE_IMSK = '{EX:1, MC:1, LD:1, default:0}; // Executable
  parameter perms_t PERM_SEA_IMSK = '{default:0};                   // Sealing

  // Decode the 6-bit compressed permission encoding to the full 12-bit permissions field.
  function automatic perms_t cheriot_expand_perms(cperms_t cperms);
    perms_t perms;
    perms = '0;

    if (cperms[4:3] == 2'b11) begin
      perms    = PERM_MRW_IMSK;
      perms.LG = cperms[0];
      perms.LM = cperms[1];
      perms.SL = cperms[2];
    end else if (cperms[4:2] == 3'b101) begin
      perms    = PERM_MRO_IMSK;
      perms.LG = cperms[0];
      perms.LM = cperms[1];
    end else if (cperms[4:0] == 5'b10000) begin
      perms    = PERM_MWO_IMSK;
    end else if (cperms[4:2] == 3'b100) begin
      perms    = PERM_MDO_IMSK;
      perms.SD = cperms[0];
      perms.LD = cperms[1];
    end else if (cperms[4:3] == 2'b01) begin
      perms    = PERM_EXE_IMSK;
      perms.LG = cperms[0];
      perms.LM = cperms[1];
      perms.SR = cperms[2];
    end else if (cperms[4:3] == 2'b00) begin
      perms    = PERM_SEA_IMSK;
      perms.US = cperms[0];
      perms.SE = cperms[1];
      perms.U0 = cperms[2];
    end

    // GL is mapped directly
    perms.GL = cperms[5];

    return perms;
  endfunction

  // True if all bits set in mask are also set in p (i.e., mask is implied by p).
  function automatic logic cheriot_perms_covers(perms_t p, perms_t mask);
    return &(PERMS_W'(p) | ~PERMS_W'(mask));
  endfunction

  // Encode the full 12-bit permissions field to the 6-bit compressed memory representation.
  function automatic cperms_t cheriot_compress_perms(perms_t perms);
    cperms_t cperms;

    cperms    = '0;
    cperms[5] = perms.GL;

    if (cheriot_perms_covers(perms, PERM_EXE_IMSK)) begin
      cperms[0]   = perms.LG;
      cperms[1]   = perms.LM;
      cperms[2]   = perms.SR;
      cperms[4:3] = 2'b01;
    end else if (cheriot_perms_covers(perms, PERM_MRW_IMSK)) begin
      cperms[0]   = perms.LG;
      cperms[1]   = perms.LM;
      cperms[2]   = perms.SL;
      cperms[4:3] = 2'b11;
    end else if (cheriot_perms_covers(perms, PERM_MRO_IMSK)) begin
      cperms[0]   = perms.LG;
      cperms[1]   = perms.LM;
      cperms[4:2] = 3'b101;
    end else if (cheriot_perms_covers(perms, PERM_MWO_IMSK)) begin
      cperms[4:0] = 5'b10000;
    end else if (perms.SD | perms.LD) begin
      cperms[0]   = perms.SD;
      cperms[1]   = perms.LD;
      cperms[4:2] = 3'b100;
    end else begin
      cperms[0]   = perms.US;
      cperms[1]   = perms.SE;
      cperms[2]   = perms.U0;
      cperms[4:3] = 2'b00;
    end

    return cperms;
  endfunction

  // Apply CLC permission-clearing rules to loaded compressed permissions
  // based on the loading capability's clrperm bits.
  function automatic cperms_t cheriot_mask_loaded_cperms(cperms_t cperms_in,
                                                         cap_clrperm_t clrperm,
                                                         logic valid_in, logic sealed);
    cperms_t cperms_out;
    logic    clr_gl, clr_lg, clr_sdlm;
    logic    unused_ctag;
    unused_ctag = clrperm.CTAG;

    clr_gl    = clrperm.GL_LG & valid_in;
    clr_lg    = clrperm.GL_LG & valid_in & ~sealed;
    clr_sdlm  = clrperm.SD_LM & valid_in & ~sealed;  // only clear SD/LM if not sealed

    cperms_out    = cperms_in;
    cperms_out[5] = cperms_in[5] & ~clr_gl;          // GL

    if (cperms_in[4:3] == 2'b11) begin
      cperms_out[0] = cperms_in[0] & ~clr_lg;        // LG
      cperms_out[1] = cperms_in[1] & ~clr_sdlm;      // LM
      cperms_out[4:2] = clr_sdlm ? 3'b101 : cperms_in[4:2];
    end else if (cperms_in[4:2] == 3'b101) begin
      cperms_out[0] = cperms_in[0] & ~clr_lg;        // LG
      cperms_out[1] = cperms_in[1] & ~clr_sdlm;      // LM
    end else if (cperms_in[4:0] == 5'b10000) begin
      // clear SD will results in NULL permission
      cperms_out[4:0] = clr_sdlm ? 5'h0 : cperms_in[4:0];
    end else if (cperms_in[4:2] == 3'b100) begin
      cperms_out[4] = ~(clr_sdlm & ~cperms_in[1]);   // must decode to 5'h0 if both ld/sd are 0.
      cperms_out[0] = cperms_in[0] & ~clr_sdlm;
    end else if (cperms_in[4:3] == 2'b01) begin
      cperms_out[0] = cperms_in[0] & ~clr_lg;        // LG
      cperms_out[1] = cperms_in[1] & ~clr_sdlm;      // LM
    end

    return cperms_out;
  endfunction

  // Expand the 4-bit compressed exponent to the 5-bit value used for bounds arithmetic.
  // Field value 15 (MAXCEXP) decodes to the effective exponent 24 (MAXEXP).
  function automatic exp_t cheriot_expand_exp(cexp_t cexp);
    return (cexp == MAXCEXP) ? MAXEXP : {1'b0, cexp};
  endfunction

  // Compress a 5-bit working exponent back to the 4-bit stored form. Effective exponent 24
  // (MAXEXP) maps to field value 15 (MAXCEXP).
  function automatic cexp_t cheriot_compress_exp(exp_t exp5);
    return (exp5 == MAXEXP) ? MAXCEXP : exp5[CEXP_W-1:0];
  endfunction

  // Return the byte length of a capability (top33 - base32), saturated at 0xFFFF_FFFF on overflow.
  function automatic logic[31:0] cheriot_cap_length (decoded_cap_t full_cap);
    logic [32:0] tmp33;
    logic [31:0] result;
    decoded_cap_t unused_full_cap;

    unused_full_cap = full_cap;
    tmp33  = full_cap.top33 - {1'b0, full_cap.base32};
    result = tmp33[32] ? 32'hffff_ffff : tmp33[31:0];

    return result;
  endfunction

  // Reconstruct a 33-bit absolute bound from a 9-bit compressed bound, correction bits, exponent,
  // and the current address.
  function automatic logic[32:0] cheriot_expand_bound33(cbound_t mant, logic [1:0] cor,
                                           exp_t exp5, logic [31:0] addr);
    logic [32:0] cor_val, mask, bound, mant_ext;

    if (cor[1]) begin
      cor_val = {33{1'b1}};   // -1 (cor[1] is the sign bit and cor=10 never occurs)
    end else begin
      cor_val = {32'h0, cor[0]};  // 0 or +1
    end

    cor_val = (cor_val << exp5) << CBOUND_W;
    mask    = (33'h1_ffff_ffff << exp5) << CBOUND_W;

    bound = ({1'b0, addr} & mask) + cor_val; // apply correction and mask to upper address bits
    mant_ext = {24'h0, mant};                // zero-extend 9-bit bound mantissa to 33 bits
    bound = bound | (mant_ext << exp5);      // merge address and bound

    return bound;
  endfunction

  // CHERIoT compressed bounds borrow their upper bits from the address. If the top (T) or address
  // lie in a different 2^(e+9) aligned region than the base (B), a correction (top cor, base cor)
  // must be applied to those upper bits.
  //
  // While applying the final correction is fast, determining which correction to apply requires
  // expensive comparisons. Therefore, we do not evaluate this on every register read. Instead, we
  // encode a 2-bit state (`cap_cor`) when the bounds or address change, and store it in the
  // register file.
  //
  // `cap_cor` encodes {top_hi XOR addr_hi, addr_hi}, where:
  // top_hi  = T < B (top is in the upper region)
  // addr_hi = addr < B (address is in the upper region)
  //
  // cap_cor | top cor | base cor | condition
  // --------+---------+----------+-------------------------------------------------
  //  2'b00  |    0    |     0    | Top and address in the same region as base
  //  2'b01  |    0    |    -1    | Top and address both in the upper region
  //  2'b10  |   +1    |     0    | Top in the upper region, address is not
  //  2'b11  |   -1    |    -1    | Address in the upper region, top is not
  function automatic cap_cor_t cheriot_compute_corrections(cbound_t top, cbound_t base,
                                                           cbound_t addr);
    logic top_hi, addr_hi;
    top_hi  = (top < base);
    addr_hi = (addr < base);
    return {top_hi ^ addr_hi, addr_hi};
  endfunction

  // Decode cap_cor into the 2-bit top correction expected by cheriot_expand_bound33: -1, 0, or +1
  // It can never be 2 (2'b10)
  function automatic logic [1:0] cheriot_get_top_correction(cap_cor_t cap_cor);
    return {cap_cor[1] & cap_cor[0], cap_cor[1]};
  endfunction

  // Decode cap_cor into the 2-bit base correction expected by cheriot_expand_bound33: -1 or 0
  // Only cap_cor[0] (addr_hi) is used. It can never be 1 or 2 (2'b01, 2'b10).
  function automatic logic [1:0] cheriot_get_base_correction(cap_cor_t cap_cor);
    logic unused_top_cor_bit;
    unused_top_cor_bit = cap_cor[1];
    return {2{cap_cor[0]}};
  endfunction

  // Update a capability's address and recompute correction fields. Invalidate the tag if not
  // representable.
  function automatic decoded_cap_t cheriot_set_address(decoded_cap_t in_cap, logic [31:0] newptr);
    decoded_cap_t         out_cap;
    exp_t                 exp5;
    logic [32:0]          ptr_minus_base;
    logic [CBOUND_W-1:0]  unused_ptr_minus_base;
    logic [32-CBOUND_W:0] high_delta, repr_mask;
    cbound_t              ptr_mantissa;

    out_cap   = in_cap;
    exp5      = cheriot_expand_exp(in_cap.cexp);
    repr_mask = {(33-CBOUND_W){1'b1}} << exp5;   // zero when exp5 == 24 (full range)

    // extend to 33 bits to capture carry
    ptr_minus_base        = {1'b0, newptr} - {1'b0, in_cap.base32};
    unused_ptr_minus_base = ptr_minus_base[CBOUND_W-1:0]; // below granularity, not needed for check
    high_delta            = ptr_minus_base[32:CBOUND_W] & repr_mask;

    if (high_delta != 0) begin
      // Bounds not representable for new pointer
      out_cap.valid = 1'b0;
    end

    ptr_mantissa    = cbound_t'(newptr >> exp5);
    out_cap.cap_cor = cheriot_compute_corrections(out_cap.top, out_cap.base, ptr_mantissa);

    return out_cap;
  endfunction

  // -----------------------------------------------------------------------------------------------
  // utility functions
  // -----------------------------------------------------------------------------------------------

  // Count the number of 1s in a thermometer-encoded 32-bit vector (N LSB-aligned ones);
  function automatic logic [5:0] cheriot_thermometer_count(logic [31:0] a32);
    logic [5:0]  count;
    logic [15:0] b32;

    if (a32[31]) count = 6'd32;
    else begin
      count[5] = 1'b0;
      count[4] = a32[15];
      b32[15:0] = count[4] ? a32[31:16] : a32[15:0];
      count[3] = b32[7];
      b32[ 7:0] = count[3] ? b32[15:8] : b32[7:0];
      count[2] = b32[3];
      b32[ 3:0] = count[2] ? b32[7:4] : b32[3:0];
      count[1] = b32[1];
      b32[ 1:0] = count[1] ? b32[3:2] : b32[1:0];
      count[0] = b32[0];
    end

    return count;
  endfunction

  // Return the number of bits needed to represent din (position of the highest set bit + 1).
  // Returns 0 if din is zero.
  function automatic logic [5:0] cheriot_msb_position(logic [31:0] din);
    logic  [5:0] count;
    logic [31:0] a32;
    int i;

    a32 = {din[31], 31'h0};
    for (i = 30; i >=  0; i--) a32[i] = a32[i+1] | din[i];
    count = cheriot_thermometer_count(a32);

    return count;
  endfunction

  // Count trailing zeros, giving the alignment exponent of an address. Returns 32 if din is zero.
  function automatic logic [5:0] cheriot_count_trailing_zeros(logic [31:0] din);
    logic  [5:0] count;
    logic [31:0] a32;
    int i;

    a32 = {31'h0, din[0]};
    for (i = 1; i < 32; i++) a32[i] = a32[i-1] | din[i];
    count = cheriot_thermometer_count(~a32);       // if input all zero, return 32

    return count;
  endfunction

  // Precompute candidate exponents and parent-bound check for a SetBounds operation (cycle 1 of 2).
  function automatic bound_req_t cheriot_prep_bounds(decoded_cap_t in_cap, logic [31:0] addr,
                                                 logic [31:0] length);
    bound_req_t   result;
    logic [5:0]   size_result;
    decoded_cap_t unused_in_cap;

    unused_in_cap   = in_cap; // We don't use all capability fields
    result.top33req = {1'b0, addr} + {1'b0, length};               // "requested" 33-bit top
    result.expb     = cheriot_count_trailing_zeros(addr);
    result.explen   = cheriot_msb_position({9'h0, length[31:9]});  // length exp without saturation

    size_result     = result.explen;
    result.exp1     = (size_result >= 6'(MAXCEXP)) ? EXP_W'(MAXEXP) : EXP_W'(size_result);

    size_result     += 6'd1;
    result.exp2     = (size_result >= 6'(MAXCEXP)) ? EXP_W'(MAXEXP) : EXP_W'(size_result);

    // moved here to share with cheriot_set_bounds_rounddown
    //   should be ok to fit this in cycle 1 since it is a straight compare
    result.in_bound = ~((result.top33req > in_cap.top33) || (addr < in_cap.base32));

    return result;
  endfunction

  // Apply a prepared bound request to set a capability's top/base/exp. req_exact=1 invalidates if
  // rounding was required. Returns the decoded capability together with the alignment mask (maska)
  // and representable length (rlen) needed by the "Adjusting to Compressed Capability Precision
  // Instructions" (CRAM/CRRL).
  function automatic bound_result_t cheriot_set_bounds_ex (decoded_cap_t in_cap, logic[31:0] addr,
                                            bound_req_t bound_req, logic req_exact);
    bound_result_t     result;
    decoded_cap_t      out_cap;
    bound_req_t        unused_bound_req;

    exp_t              exp1, exp2, exp_sel;
    logic [32:0]       top33req;
    logic [CBOUND_W:0] base1, base2, top1, top2, len1, len2;
    logic [32:0]       mask1, mask2;
    logic              ovrflw, topoff1, topoff2, topoff;
    logic              baseoff1, baseoff2, baseoff;
    logic              tophi1, tophi2, tophi;
    logic              in_bound;

    unused_bound_req = bound_req;

    out_cap  = in_cap;

    top33req = bound_req.top33req;
    exp1     = bound_req.exp1;
    exp2     = bound_req.exp2;
    in_bound = bound_req.in_bound;

    // 1st path
    mask1    = {33{1'b1}} << exp1;
    base1    = (CBOUND_W+1)'(addr >> exp1);
    topoff1  = |(top33req & ~mask1);
    baseoff1 = |({1'b0, addr} & ~mask1);
    top1     = (CBOUND_W+1)'(top33req >> exp1) + (CBOUND_W+1)'(topoff1);
    len1     = top1 - base1;
    tophi1   = (top1[8:0] >= base1[8:0]);

    // overflow detection based on 1st path
    ovrflw = len1[9];

    // 2nd path in parallel
    mask2    = {33{1'b1}} << exp2;
    base2    = (CBOUND_W+1)'(addr >> exp2);
    topoff2  = |(top33req & ~mask2);
    baseoff2 = |({1'b0, addr} & ~mask2);
    top2     = (CBOUND_W+1)'(top33req >> exp2) + (CBOUND_W+1)'(topoff2);
    len2     = top2 - base2;
    tophi2   = (top2[8:0] >= base2[8:0]);

    // select results
    if (~ovrflw) begin
      exp_sel       = exp1;
      out_cap.top   = top1[CBOUND_W-1:0];
      out_cap.base  = base1[CBOUND_W-1:0];
      result.maska  = mask1[31:0];
      result.rlen   = {22'h0, len1} << exp1;
      topoff        = topoff1;
      baseoff       = baseoff1;
      tophi         = tophi1;
    end else begin
      exp_sel       = exp2;
      out_cap.top   = top2[CBOUND_W-1:0];
      out_cap.base  = base2[CBOUND_W-1:0];
      result.maska  = mask2[31:0];
      result.rlen   = {22'h0, len2} << exp2;
      topoff        = topoff2;
      baseoff       = baseoff2;
      tophi         = tophi2;
    end

    out_cap.cexp = cheriot_compress_exp(exp_sel);

`ifdef CHERIOT_PKG_DEBUG
    $display("--- cheriot_set_bounds: exact=%x ovrflw=%x exp1=%x exp2=%x exp=%x len=%x",
             ~(topoff | baseoff), ovrflw, exp1, exp2, exp_sel, result.rlen);
    $display("--- cheriot_set_bounds: b1=%x t1=%x b2=%x t2=%x", base1, top1, base2, top2);
`endif

    // top/base correction values
    // Note the new base == addr >> exp, so addr_hi == FALSE, thus base correction == 0 as such, top
    // correction can only be 0 or 1.
    out_cap.cap_cor = tophi ? 2'b00 : 2'b10;

    if (req_exact & (topoff | baseoff)) out_cap.valid = 1'b0;

    // we used the "requested top" to verify the results against original bounds
    // also compare address >= old base 32 to handle exp=24 case
    //   exp = 24 case: can have addr < base (not covered by representibility checking);
    //   other exp cases: always addr >= base when out_cap.tag == 1
    if (~in_bound)
      out_cap.valid = 1'b0;

    result.cap = out_cap;
    return result;
  endfunction

  // Set capability bounds rounded down to the nearest representable alignment.
  function automatic decoded_cap_t cheriot_set_bounds_rounddown(decoded_cap_t in_cap,
                                                                logic[31:0] addr,
                                                                bound_req_t bound_req);
    decoded_cap_t   out_cap;
    bound_req_t     unused_bound_req;  // reads exp1/exp2 to suppress INPUT_NOT_READ lint warnings
    logic [EXP_W:0] explen, expb, exp_final;
    logic [32:0]    top33req;
    logic           in_bound;
    logic           el_gt_eb, el_gt_14, eb_gt_14;
    logic           tophi;

    unused_bound_req = bound_req;
    out_cap          = in_cap;

    top33req = bound_req.top33req;
    explen   = bound_req.explen;
    expb     = bound_req.expb;
    in_bound = bound_req.in_bound;

    el_gt_eb = (explen > expb);
    el_gt_14 = (explen > 14);
    eb_gt_14 = (expb   > 14);

    // exp_final = min(14, explen, expb). Expanded form of the ternary below:
    // if (el_gt_eb & eb_gt_14) exp_final = 14;       //  min(14, min(e_l, e_b)), el > eb, eb > 14
    // else if (el_gt_eb)       exp_final = expb;     //  min(14, min(e_l, e_b)), el > eb, eb <= 14
    // else if (el_gt_14)       exp_final = 14;       //  min(14, min(e_l, e_b)), el <= eb, el > 14
    // else                     exp_final = explen;   //  e_l,                    el <= eb, el <= 14
    exp_final = (el_gt_eb & !eb_gt_14) ? expb : (el_gt_14 ? 6'd14 : explen);

    out_cap.cexp = cheriot_compress_exp(exp_final[EXP_W-1:0]);
    out_cap.base = cbound_t'(addr >> exp_final);

    out_cap.top = (el_gt_eb | el_gt_14) ? out_cap.base - cbound_t'(1'b1) :
                                          cbound_t'(top33req >> exp_final);

    if (~in_bound) out_cap.valid = 1'b0;

    // top/base correction values
    // Note the new base == addr >> exp, so addr_hi == FALSE, thus base correction == 0 as such, top
    // correction can only be 0 or 1.
    tophi = (out_cap.top >= out_cap.base);
    out_cap.cap_cor = tophi ? 2'b00 : 2'b10;

    return out_cap;
  endfunction

  // Check if a capability's permissions correspond to a sealing capability.
  function automatic logic cheriot_is_sealing_cap(cperms_t cperms);
    logic unused_cperms_gl;
    unused_cperms_gl = cperms[5]; // GL bit not needed for sealing check
    return (cperms[4:3] == 2'b00) && (|cperms[2:0]);
  endfunction

  // Return a copy of the capability sealed with the given object type.
  function automatic decoded_cap_t cheriot_seal(decoded_cap_t in_cap, otype_t new_otype);
    decoded_cap_t out_cap;
    out_cap = in_cap;
    out_cap.otype = new_otype;
    return out_cap;
  endfunction

  // Return a copy of the capability with otype set to OTYPE_UNSEALED.
  function automatic decoded_cap_t cheriot_unseal(decoded_cap_t in_cap);
    decoded_cap_t out_cap;
    out_cap = in_cap;
    out_cap.otype = OTYPE_UNSEALED;
    return out_cap;
  endfunction

  // Return true if the capability's otype is not OTYPE_UNSEALED.
  function automatic logic cheriot_is_sealed(decoded_cap_t in_cap);
    logic result;
    decoded_cap_t unused_in_cap;
    unused_in_cap = in_cap; // bounds/perms fields not needed for seal check
    result = (in_cap.otype != OTYPE_UNSEALED);
    return result;
  endfunction

  // Decode a 3-bit otype to 4-bit form; non-zero otypes lacking EX permission are tagged in bit 3.
  function automatic logic [3:0] cheriot_decode_otype(otype_t otype3, logic perm_ex);
    logic [3:0] otype4;
    otype4 = {~perm_ex & (otype3 != 0), otype3};
    return otype4;
  endfunction

  // Decode a compressed cap_t: copy the compressed fields, expand the compressed permissions, and
  // compute the absolute top33/base32 bounds from addr.
  function automatic decoded_cap_t cheriot_decode_cap(cap_t cap, logic [31:0] addr);
    decoded_cap_t d;
    exp_t         exp5;

    exp5 = cheriot_expand_exp(cap.cexp);

    // lower fields are identical to cap_t and are copied directly
    d.cap_cor = cap.cap_cor;
    d.valid   = cap.valid;
    d.rsvd    = cap.rsvd;
    d.cperms  = cap.cperms;
    d.otype   = cap.otype;
    d.cexp    = cap.cexp;
    d.top     = cap.top;
    d.base    = cap.base;

    // upper fields: decompressed bounds and permissions
    d.perms  = cheriot_expand_perms(cap.cperms);
    d.top33  = cheriot_expand_bound33(cap.top, cheriot_get_top_correction(cap.cap_cor), exp5, addr);
    d.base32 = 32'(cheriot_expand_bound33(cap.base, cheriot_get_base_correction(cap.cap_cor), exp5,
                                          addr));

    return d;
  endfunction

  // Re-encode a decoded capability to compressed cap_t. Because the lower 35 bits of decoded_cap_t
  // are laid out identically to cap_t, this is a single downward truncation/cast (the absolute
  // bounds and expanded permissions in the upper bits are discarded).
  function automatic cap_t cheriot_encode_cap(decoded_cap_t d);
    decoded_cap_t unused_d;
    unused_d = d;
    return cap_t'(d);
  endfunction

  // Convert a decoded PCC and an exception PC address to a compressed capability for MEPC.
  function automatic cap_t cheriot_pcc_to_mepc(decoded_cap_t pcc, logic [31:0] address,
                                               logic clrtag);
    cap_t         cap;
    decoded_cap_t new_dcap;

    // Still need representability check to cover save_pc_if and save_pc_wb cases
    new_dcap = cheriot_set_address(pcc, address);

    cap = cheriot_encode_cap(new_dcap);
    if (clrtag) cap.valid = 1'b0;

    return cap;
  endfunction

  // -----------------------------------------------------------------------------------------------
  // Vector representation and casts
  // -----------------------------------------------------------------------------------------------

  localparam int unsigned BASE_LO   = 0;
  localparam int unsigned TOP_LO    = BASE_LO + CBOUND_W;   // 9
  localparam int unsigned CEXP_LO   = TOP_LO + CBOUND_W;    // 18
  localparam int unsigned OTYPE_LO  = CEXP_LO + CEXP_W;     // 22
  localparam int unsigned CPERMS_LO = OTYPE_LO + OTYPE_W;   // 25
  localparam int unsigned RSVD_LO   = CPERMS_LO + CPERMS_W; // 31

  // Decode a memory-format capability metadata word and address to cap_t, applying CLC permission
  // clearing.
  function automatic cap_t cheriot_mem_to_cap(logic [32:0] cap_mw, logic [32:0] addr33,
                                              cap_clrperm_t clrperm);
    cap_t    cap;
    exp_t    exp5;
    cperms_t cperms_mem;
    cbound_t addrmi9;
    logic    sealed;
    logic    valid_in;

    valid_in   = cap_mw[32] & addr33[32];
    cap.valid  = valid_in & ~clrperm.CTAG;

    cap.base   = cap_mw[BASE_LO+:CBOUND_W];
    cap.top    = cap_mw[TOP_LO+:CBOUND_W];
    cap.cexp   = cap_mw[CEXP_LO+:CEXP_W];
    cap.otype  = cap_mw[OTYPE_LO+:OTYPE_W];

    sealed       = (cap.otype != OTYPE_UNSEALED);
    cperms_mem   = cap_mw[CPERMS_LO+:CPERMS_W];
    cap.cperms   = cheriot_mask_loaded_cperms(cperms_mem, clrperm, cap.valid, sealed);
    exp5         = cheriot_expand_exp(cap.cexp);
    addrmi9      = cbound_t'(addr33[31:0] >> exp5);
    cap.cap_cor  = cheriot_compute_corrections(cap.top, cap.base, addrmi9);

    cap.rsvd     = cap_mw[RSVD_LO];

    return cap;
  endfunction

  // Encode a stored cap_t to memory format. The lower 33 bits of cap_t are exactly the capability
  // metadata word (tag in bit [32]), so this is a single truncation that drops the correction
  // factors.
  function automatic logic[32:0] cheriot_cap_to_mem(cap_t cap);
    logic [REGCAP_W-1:0] cap_bits;
    logic [1:0] unused_cap_corr;
    cap_bits = cap;
    unused_cap_corr = cap_bits[REGCAP_W-1:33];
    return cap_bits[32:0];
  endfunction

  // Pack a cap_t into a flat REGCAP_W-bit vector cap_t is exactly REGCAP_W bits wide, so this is a
  // direct cast.
  function automatic logic [REGCAP_W-1:0] cheriot_regcap_to_vec(cap_t cap);
    return REGCAP_W'(cap);
  endfunction

  // Unpack a flat REGCAP_W-bit vector back to a cap_t.
  function automatic cap_t cheriot_vec_to_regcap(logic [REGCAP_W-1:0] vec_in);
    return cap_t'(vec_in);
  endfunction

  // Return true if two capabilities are identical in all fields and their addresses match.
  function automatic logic cheriot_caps_equal(decoded_cap_t cap_a, decoded_cap_t cap_b,
                                              logic [31:0] addr_a, logic[31:0] addr_b);
    // expanded bounds/perms not needed for equality check
    decoded_cap_t unused_cap_a, unused_cap_b;
    unused_cap_a = cap_a;
    unused_cap_b = cap_b;
    cheriot_caps_equal = (cap_a.valid == cap_b.valid) &&
                         (cap_a.top == cap_b.top) &&
                         (cap_a.base == cap_b.base) &&
                         (cap_a.cperms == cap_b.cperms) &&
                         (cap_a.rsvd == cap_b.rsvd) &&
                         (cap_a.cexp == cap_b.cexp) &&
                         (cap_a.otype == cap_b.otype) &&
                         (addr_a == addr_b);
    return cheriot_caps_equal;
  endfunction

  // -----------------------------------------------------------------------------------------------
  // CHERIoT Decoding and ALU constants
  // -----------------------------------------------------------------------------------------------

  // CHERIoT Operator
  typedef struct packed {
    logic CSET_BOUNDS_RNDN; // CSetBoundsRoundDown
    logic CRAM;             // CRepresentableAlignmentMask
    logic CRRL;             // CRepresentableLength
    logic CAUICGP;          // AUICGP
    logic CAUIPCC;          // AUIPCC
    logic CJAL;             // JAL
    logic CJALR;            // JALR
    logic CCSR_RW;          // CSpecialRW
    logic CSTORE_CAP;       // CSC
    logic CSET_HIGH;        // CSetHigh
    logic CLOAD_CAP;        // CLC
    logic CCLEAR_TAG;       // CClearTag
    logic CSUB_CAP;         // CSub
    logic CMOVE_CAP;        // CMove
    logic CIS_EQUAL;        // CIsEqual
    logic CIS_SUBSET;       // CTestSubset
    logic CSET_BOUNDS_IMM;  // CSetBoundsImm
    logic CSET_BOUNDS_EX;   // CSetBoundsExact
    logic CSET_BOUNDS;      // CSetBounds
    logic CINC_ADDR_IMM;    // CIncAddrImm
    logic CINC_ADDR;        // CIncAddr
    logic CSET_ADDR;        // CSetAddr
    logic CAND_PERM;        // CAndPerm
    logic CUNSEAL;          // CUnseal
    logic CSEAL;            // CSeal
    logic CGET_FIELD;       // CGetPerm/Type/Base/Len/Tag/Addr/High/Top
  } cheriot_op_t;

  typedef enum logic [2:0] {
    CFIELD_PERM = 3'h0,
    CFIELD_TYPE = 3'h1,
    CFIELD_BASE = 3'h2,
    CFIELD_LEN  = 3'h3,
    CFIELD_TAG  = 3'h4,
    CFIELD_ADDR = 3'h5,
    CFIELD_HIGH = 3'h6,
    CFIELD_TOP  = 3'h7
  } cheriot_cap_field_e;

  typedef enum logic [2:0] {
    CHERIOT_ADDER_A_ZERO  = 3'h0,
    CHERIOT_ADDER_A_IMM12 = 3'h1,
    CHERIOT_ADDER_A_IMM21 = 3'h2,
    CHERIOT_ADDER_A_IMM20 = 3'h3,
    CHERIOT_ADDER_A_RS2   = 3'h4
  } cheriot_adder_a_sel_e;

  typedef enum logic [1:0] {
    CHERIOT_ADDER_B_ZERO = 2'h0,
    CHERIOT_ADDER_B_RS1  = 2'h1,
    CHERIOT_ADDER_B_PC   = 2'h2
  } cheriot_adder_b_sel_e;

  typedef enum logic [2:0] {
    SETADDR_NONE      = 3'h0,  // default: null cap, zero addr
    SETADDR_PCC_PCNXT = 3'h1,  // CJAL/CJALR: pcc cap, pc_id_nxt addr
    SETADDR_PCC_ARITH = 3'h2,  // CAUIPCC: pcc cap, addr_result
    SETADDR_RFA_ARITH = 3'h3,  // CSET_ADDR/CINC_ADDR/CINC_ADDR_IMM/CAUICGP: rf_a cap, addr_result
    SETADDR_SCR       = 3'h4   // CCSR_RW: rf_a cap, csr_wdata (only when scr_legalization=1)
  } cheriot_setaddr_sel_e;

  typedef enum logic [2:0] {
    SETBOUNDS_NONE   = 3'h0,  // default
    SETBOUNDS_RS2    = 3'h1,  // CSET_BOUNDS: newlen=rs2, not exact, cap from rs1
    SETBOUNDS_RNDN   = 3'h2,  // CSET_BOUNDS_RNDN: newlen=rs2, not exact, cap from rs1 (rounded)
    SETBOUNDS_RS2_EX = 3'h3,  // CSET_BOUNDS_EX: newlen=rs2, exact, cap from rs1
    SETBOUNDS_IMM    = 3'h4,  // CSET_BOUNDS_IMM: newlen=imm12, not exact, cap from rs1
    SETBOUNDS_CRRL   = 3'h5,  // CRRL: newlen=rs1, null cap, result=rlen
    SETBOUNDS_CRAM   = 3'h6   // CRAM: newlen=rs1, null cap, result=maska
  } cheriot_setbounds_sel_e;

  typedef enum logic [4:0] {
    CHERIOT_CSR_NULL,
    CHERIOT_CSR_RW
  } cheriot_csr_op_e;

  parameter logic [4:0] CHERIOT_SCR_MEPCC      = 5'h1f;
  parameter logic [4:0] CHERIOT_SCR_MSCRATCHC  = 5'h1e;
  parameter logic [4:0] CHERIOT_SCR_MTDC       = 5'h1d;
  parameter logic [4:0] CHERIOT_SCR_MTCC       = 5'h1c;
  parameter logic [4:0] CHERIOT_SCR_ZTOPC      = 5'h1b;
  parameter logic [4:0] CHERIOT_SCR_DSCRATCHC1 = 5'h1a;
  parameter logic [4:0] CHERIOT_SCR_DSCRATCHC0 = 5'h19;
  parameter logic [4:0] CHERIOT_SCR_DEPCC      = 5'h18;

  // permission violations
  parameter int unsigned W_PVIO = 8;

  parameter logic [2:0] PVIO_TAG   = 3'h0;
  parameter logic [2:0] PVIO_SEAL  = 3'h1;
  parameter logic [2:0] PVIO_EX    = 3'h2;
  parameter logic [2:0] PVIO_LD    = 3'h3;
  parameter logic [2:0] PVIO_SD    = 3'h4;
  parameter logic [2:0] PVIO_SC    = 3'h5;
  parameter logic [2:0] PVIO_ASR   = 3'h6;
  parameter logic [2:0] PVIO_ALIGN = 3'h7;


  // Encode permission and bounds violation flags into the CHERIoT exception cause code.
  function automatic logic [4:0] cheriot_violation_cause(logic bound_vio,
                                                         logic[W_PVIO-1:0] perm_vio_vec);
    logic [4:0] vio_cause;
    logic       unused_align_vio;

    unused_align_vio = perm_vio_vec[PVIO_ALIGN];  // alignment not mapped to a cause code yet
    if (perm_vio_vec[PVIO_TAG])
      vio_cause = 5'h2;
    else if (perm_vio_vec[PVIO_SEAL])
      vio_cause = 5'h3;
    else if (perm_vio_vec[PVIO_EX])
      vio_cause = 5'h11;
    else if (perm_vio_vec[PVIO_LD])
      vio_cause = 5'h12;
    else if (perm_vio_vec[PVIO_SD])
      vio_cause = 5'h13;
    else if (perm_vio_vec[PVIO_SC])
      vio_cause = 5'h15;
    else if (perm_vio_vec[PVIO_ASR])
      vio_cause = 5'h18;
    else if (bound_vio)
      vio_cause = 5'h1;
    else
      vio_cause = 5'h0;

    return vio_cause;
  endfunction

endpackage
