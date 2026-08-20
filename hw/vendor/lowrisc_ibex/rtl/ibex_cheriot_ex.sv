// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module ibex_cheriot_ex import ibex_cheriot_pkg::*; import ibex_pkg::*; #(
  parameter logic        WritebackStage = 1'b0
)(
   // Clock and Reset
  input  logic                   clk_i,
  input  logic                   rst_ni,

  // configuration & control
  input  ibex_mubi_t             cheriot_enable_i,
  input  logic                   debug_mode_i,

  // data forwarded from WB stage
  input  logic                   fwd_we_i,
  input  logic  [4:0]            fwd_waddr_i,
  input  logic [31:0]            fwd_wdata_i,
  input  cap_t                   fwd_wcap_i,

  // regfile interface
  input  logic  [4:0]            rf_raddr_a_i,
  input  logic [31:0]            rf_rdata_a_i,
  input  cap_t                   rf_rcap_a_i,
  input  logic  [4:0]            rf_raddr_b_i,
  input  logic [31:0]            rf_rdata_b_i,
  input  cap_t                   rf_rcap_b_i,
  input  logic  [4:0]            rf_waddr_i,

  // pcc interface
  input  decoded_cap_t           pcc_cap_i,
  output decoded_cap_t           pcc_cap_o,
  input  logic [31:0]            pc_id_i,

  // use branch_req_o also to update pcc cap
  output logic                   branch_req_o,          // update PCC (goes to cs_registers)
  output logic                   branch_req_spec_o,     // speculative branch request (go to IF)
  output logic [31:0]            branch_target_o,

  // Interface to ID stage control logic
  input  logic                   cheriot_exec_id_i,
  input  logic                   instr_first_cycle_i,   // 1st exec cycle allowing lsu_req

  // inputs from decoder
  input  logic                   instr_valid_i,
  input  logic                   instr_is_cheriot_i,
  input  logic                   instr_is_rv32lsu_i,
  input  logic                   instr_is_compressed_i,
  input  logic [11:0]            cheriot_imm12_i,
  input  logic [19:0]            cheriot_imm20_i,
  input  logic [20:0]            cheriot_imm21_i,
  input  logic  [4:0]            cheriot_cs2_dec_i,       // cs2 used for CSR address
  input  cheriot_op_t            cheriot_operator_i,
  input  cheriot_cap_field_e     cheriot_cap_field_sel_i,
  input  cheriot_adder_a_sel_e   cheriot_adder_a_sel_i,
  input  cheriot_adder_b_sel_e   cheriot_adder_b_sel_i,
  input  cheriot_setaddr_sel_e   cheriot_setaddr_sel_i,
  input  cheriot_setbounds_sel_e cheriot_setbounds_sel_i,

  // output to wb stage
  output logic                   cheriot_rf_we_o,
  output logic [31:0]            result_data_o,
  output cap_t                   result_cap_o,

  output logic                   cheriot_ex_valid_o,
  output logic                   cheriot_ex_err_o,
  output logic [11:0]            cheriot_ex_err_info_o,
  output logic                   cheriot_wb_err_o,
  output logic [15:0]            cheriot_wb_err_info_o,

  // lsu interface
  output logic                   lsu_req_o,
  output logic                   lsu_cheriot_err_o,
  output logic                   lsu_is_cap_o,
  output cap_clrperm_t           lsu_lc_clrperm_o,
  output logic                   lsu_we_o,
  output logic [31:0]            lsu_addr_o,
  output logic [1:0]             lsu_type_o,
  output logic [31:0]            lsu_wdata_o,
  output cap_t                   lsu_wcap_o,
  output logic                   lsu_sign_ext_o,

  input  logic                   addr_incr_req_i,
  input  logic [31:0]            addr_last_i,

  // LSU interface to the existing core (muxed)
  input  logic                   rv32_lsu_req_i,
  input  logic                   rv32_lsu_we_i,
  input  logic [1:0]             rv32_lsu_type_i,
  input  logic [31:0]            rv32_lsu_wdata_i,
  input  logic                   rv32_lsu_sign_ext_i,
  input  logic [31:0]            rv32_lsu_addr_i,
  output logic                   rv32_addr_incr_req_o,
  output logic [31:0]            rv32_addr_last_o,

  input  logic [31:0]            csr_rdata_i,
  input  cap_t                   csr_rcap_i,
  input  logic                   csr_mstatus_mie_i,
  output logic                   csr_access_o,
  output logic  [4:0]            csr_addr_o,
  output logic [31:0]            csr_wdata_o,
  output cap_t                   csr_wcap_o,
  output cheriot_csr_op_e        csr_op_o,
  output logic                   csr_op_en_o,
  output logic                   csr_set_mie_o,
  output logic                   csr_clr_mie_o,

  // stack highwater mark updates
  input  logic [31:0]            csr_mshwm_i,
  input  logic [31:0]            csr_mshwmb_i,
  output logic                   csr_mshwm_set_o,
  output logic [31:0]            csr_mshwm_new_o,

  input  logic [31:0]            ztop_rdata_i,
  input  cap_t                   ztop_rcap_i,

  // debug feature
  input  logic                   csr_dbg_tclr_fault_i
);

  logic               cheriot_lsu_req;
  logic               cheriot_lsu_we;
  logic [31:0]        cheriot_lsu_addr;
  logic [31:0]        cheriot_lsu_wdata;
  cap_t               cheriot_lsu_wcap;
  logic               cheriot_lsu_err;
  logic               cheriot_lsu_is_cap;

  logic [31:0]        rf_rdata_a, rf_rdata_ng_a;
  logic [31:0]        rf_rdata_b, rf_rdata_ng_b;

  cap_t               rf_rcap_a, rf_rcap_ng_a;
  cap_t               rf_rcap_b, rf_rcap_ng_b;

  decoded_cap_t       rf_fullcap_a, rf_fullcap_b;

  cap_t               csc_wcap;

  logic               is_load_cap, is_store_cap, is_cap;

  logic               addr_bound_vio;
  logic               perm_vio, perm_vio_slc;
  logic               rv32_lsu_err;
  logic               addr_bound_vio_rv32;
  logic               perm_vio_rv32;

  logic [W_PVIO-1:0]  perm_vio_vec, perm_vio_vec_rv32;

  logic  [31:0]       cs1_addr_plusimm;
  logic  [31:0]       cs1_imm;
  logic  [31:0]       addr_result;

  logic               cheriot_rf_we_raw, branch_req_raw, branch_req_spec_raw;
  logic               csr_set_mie_raw, csr_clr_mie_raw;
  logic               cheriot_ex_valid_raw, cheriot_ex_err_raw;
  logic               csr_op_en_raw;
  logic               cheriot_wb_err_raw;
  logic               cheriot_wb_err_q, cheriot_wb_err_d;
  cap_clrperm_t       cheriot_lsu_lc_clrperm;
  logic               lc_cglg, lc_csdlm, lc_ctag;
  logic  [31:0]       pc_id_nxt;

  decoded_cap_t       setaddr1_outcap, setbounds_outcap, setbounds_rndn_outcap;
  bound_result_t      setbounds_result;
  logic  [31:0]       setbounds_maska, setbounds_rlen;
  logic  [15:0]       cheriot_wb_err_info_q, cheriot_wb_err_info_d;

  logic   [4:0]       cheriot_err_cause, rv32_err_cause;
  logic   [31:0]      cpu_lsu_addr;
  logic   [31:0]      cpu_lsu_wdata;
  logic               cpu_lsu_we;
  logic               cpu_lsu_cheriot_err, cpu_lsu_is_cap;

  logic               illegal_scr_addr;
  // verilator lint_off UNOPTFLAT
  logic               scr_legalization;
  // verilator lint_on UNOPTFLAT

  decoded_cap_t       tfcap;
  perms_t             pmask;
  logic               clr_sealed;
  logic               instr_fault;
  logic               is_write, is_ztop;
  cap_t               trcap;
  logic [2:0]         seal_type;
  logic [31:0]        tmp32a, tmp32b;
  decoded_cap_t       tfcap1;
  logic [31:0]        taddr1;
  logic [31:0]        newlen;
  logic               req_exact;
  logic [31:0]        tmp_addr;
  decoded_cap_t       tfcap3;
  logic [31:0]        rv32_top_offset;
  logic [32:0]        rv32_top_bound;
  logic [31:0]        rv32_base_bound, rv32_base_chkaddr;
  logic               rv32_top_vio, rv32_base_vio;
  logic [32:0]        rv32_top_chkaddr;
  logic               rv32_top_size_ok;
  logic [32:0]        chk_top_bound;
  logic [31:0]        chk_base_bound, chk_base_chkaddr;
  logic [32:0]        chk_top_chkaddr;
  logic               chk_top_vio, chk_base_vio, chk_top_equal;
  logic               chk_cs2_bad_type;
  logic               chk_cs1_otype_0, chk_cs1_otype_1, chk_cs1_otype_45, chk_cs1_otype_23;

  // data forwarding for CHERIoT instructions
  //  - note address 0 is a read-only location per RISC-V
  always_comb begin : fwd_data_merger
    if ((rf_raddr_a_i == fwd_waddr_i) && fwd_we_i && (|rf_raddr_a_i)) begin
      rf_rdata_ng_a = fwd_wdata_i;
      rf_rcap_ng_a  = fwd_wcap_i;
    end else begin
      rf_rdata_ng_a = rf_rdata_a_i;
      rf_rcap_ng_a  = rf_rcap_a_i;
    end

    if ((rf_raddr_b_i == fwd_waddr_i) && fwd_we_i && (|rf_raddr_b_i)) begin
      rf_rdata_ng_b = fwd_wdata_i;
      rf_rcap_ng_b  = fwd_wcap_i;
    end else begin
      rf_rdata_ng_b = rf_rdata_b_i;
      rf_rcap_ng_b  = rf_rcap_b_i;
    end
  end

  // 1st level of operand gating (power-saving)
  //  - gate off the input to reg2full conversion logic
  //  - note rv32 lsu req only use cs1
  //  - may need to use don't-touch gates
  assign rf_rcap_a   = (instr_is_cheriot_i | instr_is_rv32lsu_i) ? rf_rcap_ng_a : NULL_CAP;
  assign rf_rdata_a  = (instr_is_cheriot_i | instr_is_rv32lsu_i) ? rf_rdata_ng_a : 32'h0;

  assign rf_rcap_b   = instr_is_cheriot_i ? rf_rcap_ng_b : NULL_CAP;
  assign rf_rdata_b  = instr_is_cheriot_i ? rf_rdata_ng_b : 32'h0;

  // expand the capabilities
  assign rf_fullcap_a = cheriot_decode_cap(rf_rcap_a, rf_rdata_a);
  assign rf_fullcap_b = cheriot_decode_cap(rf_rcap_b, rf_rdata_b);

  // gate these signals with cheriot_exec_id to make sure they are only active when needed
  // (only 1 cycle in all cases other than cheriot_rf_we)
  // -- safest approach and probably the right thing to do in case there is a wb_exception
  assign cheriot_rf_we_o   = cheriot_rf_we_raw & cheriot_exec_id_i;
  assign branch_req_o      = branch_req_raw & cheriot_exec_id_i;
  assign branch_req_spec_o = branch_req_spec_raw & cheriot_exec_id_i;
  assign csr_set_mie_o     = csr_set_mie_raw & cheriot_exec_id_i;
  assign csr_clr_mie_o     = csr_clr_mie_raw & cheriot_exec_id_i;
  assign csr_op_en_o       = csr_op_en_raw & cheriot_exec_id_i;

  // ex_valid only used in multicycle case
  // ex_err is used for id exceptions
  assign cheriot_ex_valid_o = cheriot_ex_valid_raw & cheriot_exec_id_i;
  assign cheriot_ex_err_o   = cheriot_ex_err_raw & cheriot_exec_id_i & ~debug_mode_i;

  if (WritebackStage) begin : gen_err_wb_stage
    assign cheriot_wb_err_o = cheriot_wb_err_q;
  end else begin : gen_err_no_wb_stage
    assign cheriot_wb_err_o = cheriot_wb_err_d;
  end

  assign cheriot_lsu_lc_clrperm = debug_mode_i ? '0 :
                                                 '{CTAG: lc_ctag, SD_LM: lc_csdlm, GL_LG: lc_cglg};

  always_comb begin : main_ex
    //default
    cheriot_rf_we_raw    = 1'b0;
    result_data_o        = 32'h0;
    result_cap_o         = NULL_CAP;
    csc_wcap             = NULL_CAP;
    cheriot_ex_valid_raw = 1'b0;
    cheriot_ex_err_raw   = 1'b0;
    cheriot_wb_err_raw   = 1'b0;
    csr_access_o         = 1'b0;
    csr_addr_o           = 5'h0;
    csr_wdata_o          = 32'h0;
    csr_wcap_o           = NULL_CAP;
    csr_op_o             = CHERIOT_CSR_NULL;
    csr_op_en_raw        = 1'b0;
    scr_legalization     = 1'b0;

    branch_req_raw       = 1'b0;
    branch_req_spec_raw  = 1'b0;
    csr_set_mie_raw      = 1'b0;
    csr_clr_mie_raw      = 1'b0;
    branch_target_o      = 32'h0;
    pcc_cap_o            = NULL_DECODED_CAP;
    tfcap                = NULL_DECODED_CAP;
    lc_cglg              = 1'b0;
    lc_csdlm             = 1'b0;
    lc_ctag              = 1'b0;

    unique case (1'b1)
      cheriot_operator_i.CGET_FIELD:
        begin
          result_cap_o         = NULL_CAP;
          cheriot_rf_we_raw    = 1'b1;
          cheriot_ex_valid_raw = 1'b1;
          unique case (cheriot_cap_field_sel_i)
            CFIELD_PERM: result_data_o = {20'h0, rf_fullcap_a.perms};
            CFIELD_TYPE: result_data_o = {28'h0,
                             cheriot_decode_otype(rf_fullcap_a.otype, rf_fullcap_a.perms.EX)};
            CFIELD_BASE: result_data_o = rf_fullcap_a.base32;
            CFIELD_TOP:  result_data_o = rf_fullcap_a.top33[32] ? 32'hffff_ffff
                                                                 : rf_fullcap_a.top33[31:0];
            CFIELD_LEN:  result_data_o = cheriot_cap_length(rf_fullcap_a);
            CFIELD_TAG:  result_data_o = {31'h0, rf_fullcap_a.valid};
            CFIELD_ADDR: result_data_o = rf_rdata_a;
            CFIELD_HIGH: result_data_o = 32'(cheriot_cap_to_mem(rf_rcap_a));
            default:     result_data_o = 32'h0;
          endcase
        end
      (cheriot_operator_i.CSEAL | cheriot_operator_i.CUNSEAL):
        begin                   // cd <-- cs1; cd.otyp <-- cs2.otype; cd.sealed <-- val
          result_data_o = rf_rdata_a;

          if (cheriot_operator_i.CSEAL)
            result_cap_o = cheriot_encode_cap(cheriot_seal(rf_fullcap_a, rf_rdata_b[OTYPE_W-1:0]));
          else begin
            tfcap          = cheriot_unseal(rf_fullcap_a);
            tfcap.perms.GL = rf_fullcap_a.perms.GL & rf_fullcap_b.perms.GL;
            tfcap.cperms   = cheriot_compress_perms(tfcap.perms);
            result_cap_o   = cheriot_encode_cap(tfcap);
          end

          result_cap_o.valid   = result_cap_o.valid & (~addr_bound_vio) & (~perm_vio);
          cheriot_rf_we_raw      = 1'b1;
          cheriot_ex_valid_raw   = 1'b1;
        end
      cheriot_operator_i.CAND_PERM:         // cd <-- cs1; cd.perm <-- cd.perm & rs2
        begin
          result_data_o = rf_rdata_a;
          tfcap         = rf_fullcap_a;
          tfcap.perms   = perms_t'(PERMS_W'(tfcap.perms) & rf_rdata_b[PERMS_W-1:0]);
          tfcap.cperms  = cheriot_compress_perms(tfcap.perms);
          // for sealed caps, clear tag unless perm mask (excluding GL) == all '1'
          pmask                = perms_t'(rf_rdata_b[PERMS_W-1:0]);
          pmask.GL             = 1'b1;
          tfcap.valid          = tfcap.valid &
                                 (~cheriot_is_sealed(rf_fullcap_a) | (&PERMS_W'(pmask)));
          result_cap_o         = cheriot_encode_cap(tfcap);
          cheriot_rf_we_raw    = 1'b1;
          cheriot_ex_valid_raw = 1'b1;
        end
      cheriot_operator_i.CSET_HIGH:         // cd <-- cs1; cd.high <-- convert(rs2)
        begin
          result_data_o        = rf_rdata_a;
          result_cap_o         = cheriot_mem_to_cap({1'b0, rf_rdata_b}, {1'b0, rf_rdata_a}, 3'h0);
          cheriot_rf_we_raw    = 1'b1;
          cheriot_ex_valid_raw = 1'b1;
        end

      // setaddr/incoffset: cd <-- cs1; cd.offset <-- rs2, or cs1.addr + rs2, or cs1.addr + imm12
      // auipcc: cd <-- pcc, cd.address <-- pcc.address + (imm20 << 12)
      (cheriot_operator_i.CSET_ADDR | cheriot_operator_i.CINC_ADDR |
       cheriot_operator_i.CINC_ADDR_IMM | cheriot_operator_i.CAUIPCC |
       cheriot_operator_i.CAUICGP):
        begin
          result_data_o        = addr_result;

          // for pointer operations, follow C convention and allow newptr == top
          clr_sealed           = (cheriot_setaddr_sel_i == SETADDR_PCC_ARITH)
                                 ? 1'b0 : cheriot_is_sealed(rf_fullcap_a);
          tfcap                = setaddr1_outcap;
          tfcap.valid          = tfcap.valid & ~clr_sealed;
          result_cap_o         = cheriot_encode_cap(tfcap);
          instr_fault          = csr_dbg_tclr_fault_i
              & (rf_fullcap_a.valid | (cheriot_setaddr_sel_i == SETADDR_PCC_ARITH))
              & ~result_cap_o.valid;
          cheriot_wb_err_raw   = instr_fault;
          cheriot_rf_we_raw    = ~instr_fault;
          cheriot_ex_valid_raw = 1'b1;
        end
      (cheriot_operator_i.CSET_BOUNDS | cheriot_operator_i.CSET_BOUNDS_IMM
       | cheriot_operator_i.CSET_BOUNDS_EX | cheriot_operator_i.CRRL
       | cheriot_operator_i.CRAM | cheriot_operator_i.CSET_BOUNDS_RNDN):
        begin                  // cd <-- cs1; cd.base <-- cs1.address, cd.len <-- rs2 or imm12
          tfcap       = (cheriot_setbounds_sel_i == SETBOUNDS_RNDN) ? setbounds_rndn_outcap
                                                                  : setbounds_outcap;
          tfcap.valid = tfcap.valid & ~cheriot_is_sealed(rf_fullcap_a);

          if (cheriot_setbounds_sel_i == SETBOUNDS_CRRL) begin
            result_data_o = setbounds_rlen;
            result_cap_o  = NULL_CAP;
          end else if (cheriot_setbounds_sel_i == SETBOUNDS_CRAM) begin
            result_data_o = setbounds_maska;
            result_cap_o  = NULL_CAP;
          end else begin
            result_data_o = rf_rdata_a;
            result_cap_o  = cheriot_encode_cap(tfcap);
          end

          cheriot_ex_valid_raw = 1'b1;
          instr_fault        = csr_dbg_tclr_fault_i & rf_fullcap_a.valid & ~result_cap_o.valid &
                               (cheriot_setbounds_sel_i == SETBOUNDS_RS2   ||
                                cheriot_setbounds_sel_i == SETBOUNDS_RS2_EX ||
                                cheriot_setbounds_sel_i == SETBOUNDS_IMM   ||
                                cheriot_setbounds_sel_i == SETBOUNDS_RNDN);
          cheriot_rf_we_raw    = ~instr_fault;
          cheriot_wb_err_raw   = instr_fault;
        end
      cheriot_operator_i.CCLEAR_TAG:         // cd <-- cs1; cd.tag <-- '0'
        begin
          result_data_o        = rf_rdata_a;
          result_cap_o         = rf_rcap_a;
          result_cap_o.valid   = 1'b0;
          cheriot_rf_we_raw    = 1'b1;
          cheriot_ex_valid_raw = 1'b1;
        end
      cheriot_operator_i.CIS_SUBSET:      // rd <-- (cs1.tag == cs2.tag) && (cs2 is_subset_of cs1)
        begin
          result_data_o        = 32'((rf_fullcap_a.valid == rf_fullcap_b.valid) &&
                                  ~addr_bound_vio && (&(rf_fullcap_a.perms | ~rf_fullcap_b.perms)));
          result_cap_o         = NULL_CAP;
          cheriot_rf_we_raw    = 1'b1;
          cheriot_ex_valid_raw = 1'b1;
        end
      cheriot_operator_i.CIS_EQUAL:       // rd <-- (cs1 == cs2)
        begin
          result_data_o =
              32'(cheriot_caps_equal(rf_fullcap_a, rf_fullcap_b, rf_rdata_a, rf_rdata_b));
          result_cap_o         = NULL_CAP;
          cheriot_rf_we_raw    = 1'b1;
          cheriot_ex_valid_raw = 1'b1;
        end
      cheriot_operator_i.CSUB_CAP:          // rd <-- cs1.addr - cs2.addr
        begin
          result_data_o        = rf_rdata_a - rf_rdata_b;
          result_cap_o         = NULL_CAP;
          cheriot_rf_we_raw    = 1'b1;
          cheriot_ex_valid_raw = 1'b1;
        end
      cheriot_operator_i.CMOVE_CAP:         // cd <-- cs1
        begin
          result_data_o        = rf_rdata_a;
          result_cap_o         = rf_rcap_a;
          cheriot_rf_we_raw    = 1'b1;
          cheriot_ex_valid_raw = 1'b1;
        end
      cheriot_operator_i.CLOAD_CAP:
        begin
          lc_cglg              = ~rf_fullcap_a.perms.LG;
          lc_csdlm             = ~rf_fullcap_a.perms.LM;
          lc_ctag              = ~rf_fullcap_a.perms.MC;

          result_data_o        = 32'h0;
          result_cap_o         = NULL_CAP;
          cheriot_rf_we_raw    = 1'b0;
          cheriot_ex_valid_raw = 1'b1;             // lsu_req_done is factored in by id_stage
          cheriot_ex_err_raw   = 1'b0;             // acc err passed to LSU, processed later in WB
        end
      cheriot_operator_i.CSTORE_CAP:
        begin
          result_data_o        = 32'h0;
          result_cap_o         = NULL_CAP;
          cheriot_rf_we_raw    = 1'b0;
          cheriot_ex_valid_raw = 1'b1;
          cheriot_ex_err_raw   = 1'b0;       // acc err passed to LSU and processed later in WB
          csc_wcap             = rf_rcap_b;
          csc_wcap.valid       = rf_rcap_b.valid & ~perm_vio_slc;
        end
      cheriot_operator_i.CCSR_RW:           // cd <-- scr; scr <-- cs1 if cs1 != C0
        begin
          is_ztop       = (cheriot_cs2_dec_i == CHERIOT_SCR_ZTOPC);
          is_write      = (rf_raddr_a_i != 0);
          instr_fault   = perm_vio | illegal_scr_addr;

          csr_access_o  = ~instr_fault;
          csr_op_o      = CHERIOT_CSR_RW;
          csr_op_en_raw = ~instr_fault && is_write && ~is_ztop;
          csr_addr_o    = cheriot_cs2_dec_i;

          if (cheriot_cs2_dec_i == CHERIOT_SCR_MTCC) begin
            // MTVEC/MTCC legalization (clear tag if checking fails)
            // The cheriot_set_address call is required to recompute cap_cor for the legalized
            // address, updating the correction values only when the trimmed address falls below
            // the lower bound. Although the capability will be invalidated here regardless,
            // recomputing ensures the resulting (untagged) capability matches the Sail reference
            // model in the case where legalization actually changes the address.
            scr_legalization = 1'b1;
            csr_wdata_o      = {rf_rdata_a[31:2], 2'b00};
            trcap            = cheriot_encode_cap(setaddr1_outcap);
            if ((rf_rdata_a[1:0] != 2'b00) || ~rf_fullcap_a.perms.EX
                || (rf_fullcap_a.otype != 0))
              trcap.valid = 1'b0;
            else
              trcap.valid = rf_fullcap_a.valid;
            csr_wcap_o = trcap;
          end else if (cheriot_cs2_dec_i == CHERIOT_SCR_MEPCC) begin
            // MEPCC legalization (clear tag if checking fails)
            // Apply the same legalization and Sail-matching logic as with MTCC above.
            scr_legalization = 1'b1;
            csr_wdata_o      = {rf_rdata_a[31:1], 1'b0};
            trcap            = cheriot_encode_cap(setaddr1_outcap);
            if ((rf_rdata_a[0] != 1'b0) || ~rf_fullcap_a.perms.EX
                || (rf_fullcap_a.otype != 0))
              trcap.valid = 1'b0;
            else
              trcap.valid = rf_fullcap_a.valid;
            csr_wcap_o = trcap;
          end else begin
            scr_legalization = 1'b0;
            csr_wdata_o      = rf_rdata_a;
            csr_wcap_o       = rf_rcap_a;
          end

          if (is_ztop) begin
            result_data_o = ztop_rdata_i;
            result_cap_o  = ztop_rcap_i;
          end else begin
            result_data_o = csr_rdata_i;
            result_cap_o  = csr_rcap_i;
          end
          cheriot_rf_we_raw    = ~instr_fault;
          cheriot_ex_valid_raw = 1'b1;
          cheriot_wb_err_raw   = instr_fault;
        end
      (cheriot_operator_i.CJALR | cheriot_operator_i.CJAL):
        begin  // cd <-- pcc; pcc <-- cs1/pc+offset; pcc.address[0] <--'0'; pcc.sealed <--'0'
          // note this is the RV32 definition of JALR arithmetic (add first then mask of lsb)
          branch_target_o = {addr_result[31:1], 1'b0};
          pcc_cap_o       = cheriot_unseal(rf_fullcap_a);
          // Note we can't directly use pc_if here
          // (link address == pc_id + delta, but pc_if should be the next executed PC
          //  (the jump target)
          //  if branch prediction works)
          result_data_o   = pc_id_nxt;
          seal_type       = csr_mstatus_mie_i ? OTYPE_SENTRY_IE_BKWD : OTYPE_SENTRY_ID_BKWD;
          tfcap           = (rf_waddr_i == 5'h1) ? cheriot_seal(setaddr1_outcap, seal_type) :
                                                   setaddr1_outcap;
          result_cap_o    = cheriot_encode_cap(tfcap);

          // problem with instr_fault: the pcc_cap.valid check causing timing issue on instr_addr_o
          // -- use the speculative version for instruction fetch
          // -- the ID exception (cheriot_ex_err) flushes the pipeline and re-set PC so
          //    the speculatively fetched instruction will be flushed
          // -- this is now mitigated since we no longer do address bound checking here
          //    but let's keep the solution for now

          instr_fault          = perm_vio;

          cheriot_rf_we_raw    = ~instr_fault;    // err -> wb exception
          branch_req_raw       = ~instr_fault & cheriot_operator_i.CJALR;    // update PCC in CSR
          branch_req_spec_raw  = ~instr_fault;    // set fetch PC

          cheriot_wb_err_raw   = instr_fault;
          cheriot_ex_err_raw   = 1'b0;
          csr_set_mie_raw      = ~instr_fault && cheriot_operator_i.CJALR &&
                                 ((rf_fullcap_a.otype == OTYPE_SENTRY_IE_FWD) ||
                                  (rf_fullcap_a.otype == OTYPE_SENTRY_IE_BKWD)) ;
          csr_clr_mie_raw      = ~instr_fault && cheriot_operator_i.CJALR &&
                                 ((rf_fullcap_a.otype == OTYPE_SENTRY_ID_FWD) ||
                                  (rf_fullcap_a.otype == OTYPE_SENTRY_ID_BKWD)) ;
          cheriot_ex_valid_raw = 1'b1;
        end
      default:;
    endcase
  end   // always_comb

  assign is_load_cap  = cheriot_operator_i.CLOAD_CAP;
  assign is_store_cap = cheriot_operator_i.CSTORE_CAP;
  assign is_cap       = cheriot_operator_i.CLOAD_CAP | cheriot_operator_i.CSTORE_CAP;

  // muxing between "normal cheriot LSU requests (clc/csc) and CLBC

  if (WritebackStage) begin : gen_lsu_req_wb_stage
    // assert LSU req until instruction is retired (req_done from LSU)
    // note if the previous instr is also a load/store, cheriot_exec_id won't be asserted
    // till WB is ready (lsu_resp for the previous isntr)
    logic unused_instr_first_cycle;
    assign unused_instr_first_cycle = instr_first_cycle_i;  // not needed with WB stage
    assign cheriot_lsu_req = is_cap & cheriot_exec_id_i;
  end else begin : gen_lsu_req_no_wb_stage
    // no WB stage, only assert req in the first_cycle phase of the instruction
    // (consistent with the RV32 load/store instructions)
    // Here instruction won't complete till lsu_resp_valid in this case,
    // keeping lsu_req asserted causes problem as LSU sees it as a new request
    assign cheriot_lsu_req = is_cap & cheriot_exec_id_i & instr_first_cycle_i;
  end

  assign cheriot_lsu_we     = is_store_cap;
  assign cheriot_lsu_addr   = cs1_addr_plusimm + {29'h0, addr_incr_req_i, 2'b00};
  assign cheriot_lsu_is_cap = is_cap;

  assign cheriot_lsu_wdata  = is_store_cap ? rf_rdata_b : 32'h0;
  assign cheriot_lsu_wcap   = is_store_cap  ? csc_wcap : NULL_CAP;

  // RS1/CS1+offset is
  //  keep this separate to help timing on the memory interface
  //   - the starting address for cheriot L*CAP/S*CAP instructions
  assign cs1_imm = (is_cap | cheriot_operator_i.CJALR) ?
      {{20{cheriot_imm12_i[11]}}, cheriot_imm12_i} : '0;

  assign cs1_addr_plusimm = rf_rdata_a + cs1_imm;

  assign pc_id_nxt = pc_id_i + (instr_is_compressed_i ? 32'd2 : 32'd4);

  //
  // shared adder for address calculation
  //
  always_comb begin : shared_adder
    unique case (cheriot_adder_a_sel_i)
      CHERIOT_ADDER_A_IMM12: tmp32a = {{20{cheriot_imm12_i[11]}}, cheriot_imm12_i};
      CHERIOT_ADDER_A_IMM21: tmp32a = {{11{cheriot_imm21_i[20]}}, cheriot_imm21_i};
      CHERIOT_ADDER_A_IMM20: tmp32a = {cheriot_imm20_i[19], cheriot_imm20_i, 11'h0};
      CHERIOT_ADDER_A_RS2:   tmp32a = rf_rdata_b;
      default:             tmp32a = 32'h0;
    endcase

    unique case (cheriot_adder_b_sel_i)
      CHERIOT_ADDER_B_RS1: tmp32b = rf_rdata_a;
      CHERIOT_ADDER_B_PC:  tmp32b = pc_id_i;
      default:           tmp32b = 32'h0;
    endcase

    addr_result = tmp32a + tmp32b;
  end

  //
  // Big combinational functions
  //  - break out to make sure we can properly gate off operands to save power
  //
  always_comb begin: set_address_comb
    if (cheriot_setaddr_sel_i == SETADDR_PCC_PCNXT) begin
      tfcap1 = pcc_cap_i;
      taddr1 = pc_id_nxt;
    end else if (cheriot_setaddr_sel_i == SETADDR_PCC_ARITH) begin
      tfcap1 = pcc_cap_i;
      taddr1 = addr_result;
    end else if (cheriot_setaddr_sel_i == SETADDR_RFA_ARITH) begin
      tfcap1 = rf_fullcap_a;
      taddr1 = addr_result;
    end else if ((cheriot_setaddr_sel_i == SETADDR_SCR) && scr_legalization) begin
      tfcap1 = rf_fullcap_a;
      taddr1 = csr_wdata_o;
    end else begin
      tfcap1 = NULL_DECODED_CAP;
      taddr1 = 32'h0;
    end

    setaddr1_outcap = cheriot_set_address(tfcap1, taddr1);
  end

  bound_req_t bound_req;

  always_comb begin: set_bounds_comb
    if (cheriot_setbounds_sel_i == SETBOUNDS_CRRL ||
        cheriot_setbounds_sel_i == SETBOUNDS_CRAM) begin
      newlen    = rf_rdata_a;
      req_exact = 1'b0;
      tfcap3    = NULL_DECODED_CAP;
      tmp_addr  = 32'h0;
    end else if (cheriot_setbounds_sel_i == SETBOUNDS_IMM) begin
      newlen    = 32'(cheriot_imm12_i);  // unsigned imm
      req_exact = 1'b0;
      tfcap3    = rf_fullcap_a;
      tmp_addr  = rf_rdata_a;
    end else if (cheriot_setbounds_sel_i != SETBOUNDS_NONE) begin
      // RS2, RS2_EX, RNDN
      newlen    = rf_rdata_b;
      req_exact = (cheriot_setbounds_sel_i == SETBOUNDS_RS2_EX);
      tfcap3    = rf_fullcap_a;
      tmp_addr  = rf_rdata_a;
    end else begin
      newlen    = 32'h0;
      req_exact = 1'b0;
      tfcap3    = NULL_DECODED_CAP;
      tmp_addr  = 32'h0;
    end

    bound_req = cheriot_prep_bounds(tfcap3, tmp_addr, newlen);

    // cheriot_set_bounds_ex returns the decoded capability plus maska/rlen (consumed by CRAM/CRRL)
    setbounds_result = cheriot_set_bounds_ex(tfcap3, tmp_addr, bound_req, req_exact);
    setbounds_outcap = setbounds_result.cap;
    setbounds_maska  = setbounds_result.maska;
    setbounds_rlen   = setbounds_result.rlen;

    setbounds_rndn_outcap = cheriot_set_bounds_rounddown(tfcap3, tmp_addr, bound_req);
  end



  // address bound and permission checks for
  //    - cheriot no-LSU instructions
  //    - cheriot LSU (cap) instructions (including internal instr like LBC)
  //    - RV32  LSU (data) instructions
  // this is a architectural access check (apply to the whole duration of an instruction)
  //    - based on architectural capability registers and addresses

  // - orginally we combine checking for CHERIoT and RV32 but it caused a combi loop
  //   that goes from instr_executing -> rv32_lsu_req -> lsu_error ->
  //   cheriot_ex_err -> instr_executing
  //   it's not a real runtime issue but it does confuses timing tools so let's split for now.
  //   Besides - note checking/lsu_cheriot_err_o is one timing critical path
  logic [31:0] rv32_ls_chkaddr;
  assign rv32_ls_chkaddr = rv32_lsu_addr_i;

  always_comb begin : check_rv32
    // generate the address used to check top bound violation
    rv32_base_chkaddr = rv32_ls_chkaddr;

    if (rv32_lsu_type_i == 2'b00) begin
      rv32_top_offset  = 32'h4;
      rv32_top_size_ok = |rf_fullcap_a.top33[32:2];     // at least 4 bytes
    end else if (rv32_lsu_type_i == 2'b01) begin
      rv32_top_offset  = 32'h2;
      rv32_top_size_ok = |rf_fullcap_a.top33[32:1];
    end else begin
      rv32_top_offset  = 32'h1;
      rv32_top_size_ok = |rf_fullcap_a.top33[32:0];
    end

    rv32_top_chkaddr = {1'b0, rv32_base_chkaddr};


    rv32_top_bound  = rf_fullcap_a.top33 - {1'b0, rv32_top_offset};
    rv32_base_bound = rf_fullcap_a.base32;

    rv32_top_vio  = (rv32_top_chkaddr  > rv32_top_bound) || ~rv32_top_size_ok;
    rv32_base_vio = (rv32_base_chkaddr < rv32_base_bound);

    // timing critical (data_req_o) path - don't add any unnecssary terms.
    // we will chose with is_cheriot on the LSU interface later.
    //   for unaligned access, only check the starting (1st) address
    //   (if there is an error, addr_incr_req won't be thre anyway
    addr_bound_vio_rv32 =  (rv32_top_vio | rv32_base_vio) & ~addr_incr_req_i ;

    // main permission logic
    perm_vio_vec_rv32 = '0;

    perm_vio_vec_rv32[PVIO_TAG]  = ~rf_fullcap_a.valid;
    perm_vio_vec_rv32[PVIO_SEAL] = cheriot_is_sealed(rf_fullcap_a);
    perm_vio_vec_rv32[PVIO_LD]   = ((~rv32_lsu_we_i) && (~rf_fullcap_a.perms.LD));
    perm_vio_vec_rv32[PVIO_SD]   = (rv32_lsu_we_i && (~rf_fullcap_a.perms.SD));

    perm_vio_rv32 =  |perm_vio_vec_rv32;
  end

  assign rv32_lsu_err = (cheriot_enable_i == IbexMuBiOn) & ~debug_mode_i
                        & (addr_bound_vio_rv32 | perm_vio_rv32);

  // CHERIoT instr address bound checking
  //   -- we choose to centralize the address bound checking here
  //      so that we can mux the inputs and save some area


  logic [31:0] cheriot_ls_chkaddr;
  assign cheriot_ls_chkaddr = cs1_addr_plusimm;

  always_comb begin : check_cheriot
    // generate the address used to check top bound violation
    if (cheriot_operator_i.CSEAL)
      chk_base_chkaddr = rf_rdata_b;           // cs2.address
    else if (cheriot_operator_i.CUNSEAL)
      // inCapBounds(cs2_val, zero_extend(cs1_val.otype), 1)
      chk_base_chkaddr = {28'h0, cheriot_decode_otype(rf_fullcap_a.otype, rf_fullcap_a.perms.EX)};
    else if (cheriot_operator_i.CIS_SUBSET)
      chk_base_chkaddr = rf_fullcap_b.base32;  // cs2.base32
    else   // CLC/CSC
      chk_base_chkaddr = cheriot_ls_chkaddr;     // cs1.address + offset

    if (cheriot_operator_i.CIS_SUBSET)
      chk_top_chkaddr = rf_fullcap_b.top33;
    else if (is_cap)  // CLC/CSC
      chk_top_chkaddr = {1'b0, chk_base_chkaddr[31:3], 3'b000};
    else
      chk_top_chkaddr = {1'b0, chk_base_chkaddr};

    if (cheriot_operator_i.CSEAL | cheriot_operator_i.CUNSEAL) begin
      chk_top_bound  = rf_fullcap_b.top33;
      chk_base_bound = rf_fullcap_b.base32;
    end else if (is_cap) begin // CLC/CSC
      chk_top_bound  = {rf_fullcap_a.top33[32:3], 3'b000};       // 8-byte aligned access only
      chk_base_bound = rf_fullcap_a.base32;
    end else begin
      chk_top_bound  = rf_fullcap_a.top33;
      chk_base_bound = rf_fullcap_a.base32;
    end

    chk_top_vio   = (chk_top_chkaddr  > chk_top_bound);
    chk_base_vio  = (chk_base_chkaddr < chk_base_bound);
    chk_top_equal = (chk_top_chkaddr == chk_top_bound);

    if (debug_mode_i)
      addr_bound_vio = 1'b0;
    else if (is_cap)
      addr_bound_vio = chk_top_vio | chk_base_vio | chk_top_equal;
    else if (cheriot_operator_i.CIS_SUBSET)
      addr_bound_vio = chk_top_vio | chk_base_vio;
    else if (cheriot_operator_i.CSEAL | cheriot_operator_i.CUNSEAL)
      addr_bound_vio = chk_top_vio | chk_base_vio | chk_top_equal;
    else
      addr_bound_vio = 1'b0;

    // main permission logic
    perm_vio_vec     = '0;
    perm_vio         = 0;
    perm_vio_slc     = 0;
    chk_cs2_bad_type = 1'b0;
    illegal_scr_addr = 1'b0;

    // otype_1: forward sentry; otype_23: forward inherit sentry; otype_45: backward sentry;
    chk_cs1_otype_0  = (rf_fullcap_a.otype == OTYPE_UNSEALED);
    chk_cs1_otype_1  = rf_fullcap_a.perms.EX & (rf_fullcap_a.otype == OTYPE_SENTRY_II_FWD);
    chk_cs1_otype_23 = rf_fullcap_a.perms.EX
                       & ((rf_fullcap_a.otype == OTYPE_SENTRY_ID_FWD) ||
                          (rf_fullcap_a.otype == OTYPE_SENTRY_IE_FWD));
    chk_cs1_otype_45 = rf_fullcap_a.perms.EX
                       & ((rf_fullcap_a.otype == OTYPE_SENTRY_ID_BKWD) ||
                          (rf_fullcap_a.otype == OTYPE_SENTRY_IE_BKWD));

    // note cseal/unseal/cis_subject doesn't generate exceptions,
    // so for all exceptions, violations can always be attributed to cs1, thus no need to
    // further split
    // exceptions based on source operands.
    if (is_load_cap) begin
      perm_vio_vec[PVIO_TAG]   = ~rf_fullcap_a.valid;
      perm_vio_vec[PVIO_SEAL]  = cheriot_is_sealed(rf_fullcap_a);
      perm_vio_vec[PVIO_LD]    = ~rf_fullcap_a.perms.LD;
      perm_vio_vec[PVIO_ALIGN] = (cheriot_ls_chkaddr[2:0] != 0);
    end else if (is_store_cap) begin
      perm_vio_vec[PVIO_TAG]   = ~rf_fullcap_a.valid;
      perm_vio_vec[PVIO_SEAL]  = cheriot_is_sealed(rf_fullcap_a);
      perm_vio_vec[PVIO_SD]    = ~rf_fullcap_a.perms.SD;
      perm_vio_vec[PVIO_SC]    = (~rf_fullcap_a.perms.MC && rf_fullcap_b.valid);
      perm_vio_vec[PVIO_ALIGN] = (cheriot_ls_chkaddr[2:0] != 0);
      perm_vio_slc             = ~rf_fullcap_a.perms.SL && rf_fullcap_b.valid &&
                                (~rf_fullcap_b.perms.GL) ;
    end else if (cheriot_operator_i.CSEAL) begin
      chk_cs2_bad_type = rf_fullcap_a.perms.EX ?
                         ((rf_rdata_b[31:3] != 0) || (rf_rdata_b[2:0] == 0)) :
                         ((|rf_rdata_b[31:4]) || (rf_rdata_b[3:0] <= 8));
      // cs2.addr check : ex: 0-7, non-ex: 9-15
      perm_vio_vec[PVIO_TAG]   = ~rf_fullcap_b.valid;
      perm_vio_vec[PVIO_SEAL]  = cheriot_is_sealed(rf_fullcap_a) ||
                                  cheriot_is_sealed(rf_fullcap_b) ||
                                  (~rf_fullcap_b.perms.SE) || chk_cs2_bad_type;
    end else if (cheriot_operator_i.CUNSEAL) begin
      perm_vio_vec[PVIO_TAG]   = ~rf_fullcap_b.valid;
      perm_vio_vec[PVIO_SEAL]  = (~cheriot_is_sealed(rf_fullcap_a)) ||
                                 cheriot_is_sealed(rf_fullcap_b) ||
                                 (~rf_fullcap_b.perms.US);
    end else if (cheriot_operator_i.CJALR) begin
      perm_vio_vec[PVIO_TAG]   = ~rf_fullcap_a.valid;
      perm_vio_vec[PVIO_SEAL]  = (cheriot_is_sealed(rf_fullcap_a) && (cheriot_imm12_i != 0)) ||
                                 ~(((rf_waddr_i == 0) && (rf_raddr_a_i == 5'h1)
                                    && chk_cs1_otype_45) ||
                                   ((rf_waddr_i == 0) && (rf_raddr_a_i != 5'h1)
                                    && (chk_cs1_otype_0 || chk_cs1_otype_1)) ||
                                   ((rf_waddr_i == 5'h1) && (chk_cs1_otype_0 | chk_cs1_otype_23)) ||
                                   ((rf_waddr_i != 0) && (chk_cs1_otype_0 | chk_cs1_otype_1)));

      perm_vio_vec[PVIO_EX]    = ~rf_fullcap_a.perms.EX;
    end else if (cheriot_operator_i.CCSR_RW) begin
      perm_vio_vec[PVIO_ASR]   = ~pcc_cap_i.perms.SR;
      illegal_scr_addr         = (csr_addr_o < 24) | (csr_addr_o == 27) |
                                 (~debug_mode_i & (csr_addr_o < 28));
    end else begin
      perm_vio_vec = '0;
    end

    perm_vio = | perm_vio_vec;

  end

  // qualified by lsu_req later
  // store_local error only causes tag clearing unless escalated to fault for debugging
  assign cheriot_lsu_err = (cheriot_enable_i == IbexMuBiOn) & ~debug_mode_i &
                           (addr_bound_vio | perm_vio | (csr_dbg_tclr_fault_i & perm_vio_slc));

  //
  // fault case mtval generation
  // report to csr as mtval
  logic ls_addr_misaligned_only;

  assign cheriot_ex_err_info_o = 12'h0;           // no ex stage cheriot error currently
  assign cheriot_wb_err_info_o = cheriot_wb_err_info_q;

  assign cheriot_wb_err_d      = cheriot_wb_err_raw & cheriot_exec_id_i
                                 & cheriot_ex_valid_raw & ~debug_mode_i;

  // addr_bound_vio is the timing optimized version (gating data_req)
  // However we need to generate full version of addr_bound_vio to match the sail exception
  // priority definition (bound_vio has higher priority over alignment_error).
  // this has less timing impact since it goes to a flop stage
  logic addr_bound_vio_ext;
  logic [32:0] cheriot_top_chkaddr_ext;

  assign cheriot_top_chkaddr_ext = cheriot_ls_chkaddr + 33'd8;   // extend to 33 bit for compare
  assign addr_bound_vio_ext = is_cap
                              ? addr_bound_vio | (cheriot_top_chkaddr_ext > rf_fullcap_a.top33)
                              : addr_bound_vio;

  always_comb begin : err_cause_comb
    cheriot_err_cause = cheriot_violation_cause(addr_bound_vio_ext, perm_vio_vec);
    rv32_err_cause    = cheriot_violation_cause(addr_bound_vio_rv32, perm_vio_vec_rv32);


    ls_addr_misaligned_only = perm_vio_vec[PVIO_ALIGN]
                              && (perm_vio_vec[PVIO_ALIGN-1:0] == 0) && ~addr_bound_vio_ext;

    // cheriot_wb_err_raw is already qualified by instr
    // bit 15:13: reserved
    // bit 12: illegal_scr_addr
    // bit 11: alignment error (load/store)
    // bit 10:0 mtval as defined by CHERIoT arch spec
    if (cheriot_operator_i.CCSR_RW & cheriot_wb_err_raw & illegal_scr_addr & cheriot_exec_id_i)
      // cspecialrw trap, illegal addr, treated as illegal_insn
      cheriot_wb_err_info_d = {3'h0, 1'b1, 12'h0};
    else if (cheriot_operator_i.CCSR_RW & cheriot_wb_err_raw & cheriot_exec_id_i)
      // cspecialrw traps, PERM_SR
      cheriot_wb_err_info_d = {5'h0, 1'b1, cheriot_cs2_dec_i, cheriot_err_cause};
    else if (cheriot_wb_err_raw  & cheriot_exec_id_i)
      cheriot_wb_err_info_d = {5'h0, 1'b0, rf_raddr_a_i, cheriot_err_cause};
    else if ((is_load_cap | is_store_cap) & cheriot_lsu_err & cheriot_exec_id_i)
      cheriot_wb_err_info_d =
          {4'h0, ls_addr_misaligned_only, 1'b0, rf_raddr_a_i, cheriot_err_cause};
    else if (rv32_lsu_req_i & rv32_lsu_err)
      cheriot_wb_err_info_d = {5'h0, 1'b0, rf_raddr_a_i, rv32_err_cause};
    else
      cheriot_wb_err_info_d = cheriot_wb_err_info_q;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cheriot_wb_err_q      <= 1'b0;
      cheriot_wb_err_info_q <= '0;
    end else begin
      // Simple flop here works since
      //  -- cheriot_wb_err is gated by cheriot_exec_id/ex_valid
      //  --  all non-load/store cheriot instructions that can generate exceptions
      //      only takes 1 cycle in ID/EX stage
      //  -- faulted non-load/store instruction can only stay 1 cycle in wb_stage
      cheriot_wb_err_q      <= cheriot_wb_err_d;
      cheriot_wb_err_info_q <= cheriot_wb_err_info_d;
    end
  end

  //
  // muxing in cheriot LSU signals with the rv32 signals
  //
  assign lsu_req_o           = (instr_is_cheriot_i ? cheriot_lsu_req : rv32_lsu_req_i);

  assign cpu_lsu_cheriot_err = instr_is_cheriot_i ? cheriot_lsu_err : rv32_lsu_err;
  assign cpu_lsu_addr        = instr_is_cheriot_i ? cheriot_lsu_addr : rv32_lsu_addr_i;
  assign cpu_lsu_we          = instr_is_cheriot_i ? cheriot_lsu_we : rv32_lsu_we_i;
  assign cpu_lsu_wdata       = instr_is_cheriot_i ? cheriot_lsu_wdata : rv32_lsu_wdata_i;
  assign cpu_lsu_is_cap      = instr_is_cheriot_i & cheriot_lsu_is_cap;

  assign lsu_cheriot_err_o   = cpu_lsu_cheriot_err;
  assign lsu_we_o            = cpu_lsu_we;
  assign lsu_addr_o          = cpu_lsu_addr;
  assign lsu_wdata_o         = cpu_lsu_wdata;
  assign lsu_is_cap_o        = cpu_lsu_is_cap;

  assign lsu_lc_clrperm_o    = instr_is_cheriot_i ? cheriot_lsu_lc_clrperm : '0;
  assign lsu_type_o          = ~instr_is_cheriot_i ? rv32_lsu_type_i : 2'b00;
  assign lsu_wcap_o          = instr_is_cheriot_i ? cheriot_lsu_wcap    : NULL_CAP;
  assign lsu_sign_ext_o      = ~instr_is_cheriot_i ? rv32_lsu_sign_ext_i : 1'b0;

  // rv32 core side signals
  // request phase: be nice and mux using the current EX instruction to select

  // addr_incr:
  //  -- must qualify addr_incr otherwise it goes to ALU and mess up non-LSU instructions
  //  -- however for LEC to gate this with cheriot_enable_i, otherwise illegal_insn will
  //     feed into addr logic
  //     since illegal_insn goes into instr_is_rv32lsu
  assign rv32_addr_incr_req_o = ((cheriot_enable_i != IbexMuBiOn) | instr_is_rv32lsu_i)
                                ? addr_incr_req_i : 1'b0;

  assign rv32_addr_last_o     = addr_last_i;

  // req_done, resp_valid, load/store_err will be directly from LSU

  //
  // Stack high watermark CSR update
  //

  // Notes,
  //  - this should also take care of unaligned access (which increases addr only)
  //    (although stack access should not have any)
  //  - it's also ok if the prev instr gets faulted in WB, since stall_mem/data_req_allowed
  //    logic ensures
  //    that lsu_req won't be issued till memory response/error comes back
  //  - what if the instruction gets faulted later in WB stage? Also fine since worst case
  //    even if HM is
  //    too aggressive we will just have to spend more time zeroing out more stack area.

  assign csr_mshwm_set_o = lsu_req_o & ~lsu_cheriot_err_o & lsu_we_o
                           & (lsu_addr_o[31:4] >= csr_mshwmb_i[31:4])
                           & (lsu_addr_o[31:4] < csr_mshwm_i[31:4]);
  assign csr_mshwm_new_o = {lsu_addr_o[31:4], 4'h0};



  //
  // debug signal for FPGA only
  //
  logic unused_dbg_status;
  logic unused_dbg_cs1_vec, unused_dbg_cs2_vec, unused_dbg_cd_vec;

  assign unused_dbg_status = |{instr_is_rv32lsu_i, rv32_lsu_req_i, rv32_lsu_we_i,  rv32_lsu_err,
                               cheriot_exec_id_i, cheriot_lsu_err, rf_fullcap_a.valid,
                               result_cap_o.valid, addr_bound_vio, perm_vio, addr_bound_vio_rv32,
                               perm_vio_rv32};

  assign unused_dbg_cs1_vec = |{rf_fullcap_a.cap_cor,
                                cheriot_expand_exp(rf_fullcap_a.cexp),
                                rf_fullcap_a.top, rf_fullcap_a.base,
                                rf_fullcap_a.otype, rf_fullcap_a.cperms,
                                rf_rdata_a};

  assign unused_dbg_cs2_vec = |{rf_fullcap_b.cap_cor,
                                cheriot_expand_exp(rf_fullcap_b.cexp),
                                rf_fullcap_b.top, rf_fullcap_b.base,
                                rf_fullcap_b.otype, rf_fullcap_b.cperms,
                                rf_rdata_b};

  assign unused_dbg_cd_vec = |{result_cap_o.cap_cor,
                               cheriot_expand_exp(result_cap_o.cexp),
                               result_cap_o.top, result_cap_o.base,
                               result_cap_o.otype, result_cap_o.cperms,
                               result_data_o};

  logic unused_cheriot_ex_signals;
  assign unused_cheriot_ex_signals = |{instr_valid_i, csr_mshwm_i[3:0],
                                       csr_mshwmb_i[3:0], cheriot_wb_err_q};

endmodule : ibex_cheriot_ex
