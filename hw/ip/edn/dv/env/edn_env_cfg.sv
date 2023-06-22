// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_env_cfg extends cip_base_env_cfg #(.RAL_T(edn_reg_block));

  // external component cfgs
  csrng_agent_cfg   m_csrng_agent_cfg;
  push_pull_agent_cfg#(.HostDataWidth(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH))
      m_endpoint_agent_cfg[MAX_NUM_ENDPOINTS];

  `uvm_object_utils_begin(edn_env_cfg)
    `uvm_field_object(m_csrng_agent_cfg, UVM_DEFAULT)
    for (int i = 0; i < MAX_NUM_ENDPOINTS; i++) begin
      `uvm_field_object(m_endpoint_agent_cfg[i], UVM_DEFAULT)
    end
  `uvm_object_utils_end
  `uvm_object_new

  // handle to edn assert interface
  virtual edn_assert_if edn_assert_vif;
  // handle to edn path interface
  virtual edn_if edn_vif;

  // Variables
  uint   reseed_cnt, generate_cnt, generate_between_reseeds_cnt;

  bit abort_sw_cmd = 0;

  // Knobs & Weights
  uint   enable_pct, boot_req_mode_pct, auto_req_mode_pct, cmd_fifo_rst_pct,
         force_disable_pct,
         min_num_boot_reqs, max_num_boot_reqs,
         min_num_ep_reqs, max_num_ep_reqs,
         invalid_mubi4_pct;

  bit    use_invalid_mubi;

  rand mubi4_t   enable, boot_req_mode, auto_req_mode, cmd_fifo_rst;
  rand uint      num_endpoints, num_boot_reqs;
  rand bit       force_disable;
  rand bit [csrng_pkg::CSRNG_CMD_WIDTH - 1:0]   boot_ins_cmd, boot_gen_cmd;

  rand fatal_err_e      which_fatal_err;
  rand err_code_e       which_err_code;
  rand which_fifo_e     which_fifo;
  rand which_fifo_err_e which_fifo_err;
  rand invalid_mubi_e   which_invalid_mubi;

  // Constraints
  // TODO: utilize suggestions in PR9535 to generate "other" values when testing alerts
  constraint force_disable_c {force_disable dist {
    1 :/ force_disable_pct,
    0 :/ (100 - force_disable_pct) };}
  constraint enable_c {enable dist {
    MuBi4True  :/ enable_pct,
    MuBi4False :/ (100 - enable_pct) };}
  constraint cmd_fifo_rst_c {cmd_fifo_rst dist {
    MuBi4True  :/ cmd_fifo_rst_pct,
    MuBi4False :/ (100 - cmd_fifo_rst_pct) };}
  constraint num_endpoints_c {num_endpoints dist {
    MIN_NUM_ENDPOINTS :/ 40,
    MAX_NUM_ENDPOINTS :/ 40,
    [MIN_NUM_ENDPOINTS + 1:MAX_NUM_ENDPOINTS - 1] :/ 20 };}
  constraint req_mode_c {{boot_req_mode, auto_req_mode} dist {
    {MuBi4True, MuBi4False}  :/ boot_req_mode_pct,
    {MuBi4False, MuBi4True}  :/ auto_req_mode_pct,
    {MuBi4False, MuBi4False} :/ (100 - boot_req_mode_pct - auto_req_mode_pct) };

    num_boot_reqs inside { [min_num_boot_reqs:max_num_boot_reqs] };}

  constraint which_err_code_c {which_err_code dist {
    // Certain error codes are more interesting for coverage, so give each of them a higher weight.
    edn_ack_sm_err  :/ 5,
    edn_main_sm_err :/ 5,
    edn_cntr_err    :/ 5
    // All other error codes will implicitly get a weight of 1.
  };}

  // Functions
  function void post_randomize();
    if (use_invalid_mubi) begin
      prim_mubi_pkg::mubi4_t invalid_mubi_val;
      invalid_mubi_val = get_rand_mubi4_val(.t_weight(0), .f_weight(0), .other_weight(1));
      case (which_invalid_mubi)
        invalid_edn_enable: enable = invalid_mubi_val;
        invalid_boot_req_mode: boot_req_mode = invalid_mubi_val;
        invalid_auto_req_mode: auto_req_mode = invalid_mubi_val;
        invalid_cmd_fifo_rst: cmd_fifo_rst = invalid_mubi_val;
        default: `uvm_fatal(`gfn, "Invalid case! (bug in environment)")
      endcase // case (which_invalid_mubi)
    end
  endfunction // post_randomize

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = edn_env_pkg::LIST_OF_ALERTS;
    tl_intg_alert_name = "fatal_alert";
    sec_cm_alert_name = "fatal_alert";
    super.initialize(csr_base_addr);

    // create config objects
    m_csrng_agent_cfg = csrng_agent_cfg::type_id::create("m_csrng_genbits_agent_cfg");

    for (int i = 0; i < MAX_NUM_ENDPOINTS; i++) begin
      m_endpoint_agent_cfg[i] = push_pull_agent_cfg#(.HostDataWidth(edn_pkg::
                                FIPS_ENDPOINT_BUS_WIDTH))::type_id::create
                                ($sformatf("m_endpoint_agent_cfg[%0d]", i));
    end

    // set num_interrupts & num_alerts
    begin
      uvm_reg rg = ral.get_reg_by_name("intr_state");
      if (rg != null) begin
        num_interrupts = ral.intr_state.get_n_used_bits();
      end
    end

    // get edn assert interface handle
    if (!uvm_config_db#(virtual edn_assert_if)::
        get(null, "*.env" , "edn_assert_vif", edn_assert_vif)) begin
      `uvm_fatal(`gfn, $sformatf("FAILED TO GET HANDLE TO ASSERT IF"))
    end

    // only support 1 outstanding TL item
    m_tl_agent_cfg.max_outstanding_req = 1;
  endfunction

  virtual function string convert2string();
    string str = "";
    str = {str, "\n"};
    str = {str,  $sformatf("\n\t |******************* edn_env_cfg *********************| \t")};
    str = {str,  $sformatf("\n\t |***** enable                       : %10s *****| \t",
        enable.name())};
    str = {str,  $sformatf("\n\t |***** boot_req_mode                : %10s *****| \t",
        boot_req_mode.name())};
    str = {str,  $sformatf("\n\t |***** auto_req_mode                : %10s *****| \t",
        auto_req_mode.name())};
    str = {str,  $sformatf("\n\t |***** num_endpoints                : %10d *****| \t",
        num_endpoints)};
    str = {str,  $sformatf("\n\t |***** num_boot_reqs                : %10d *****| \t",
        num_boot_reqs)};
    str = {str,  $sformatf("\n\t |***** force_disable                : %10d *****| \t",
        force_disable)};
    str = {str,  $sformatf("\n\t |------------------- knobs ---------------------------| \t")};
    str = {str,  $sformatf("\n\t |***** enable_pct                   : %10d *****| \t",
        enable_pct)};
    str = {str,  $sformatf("\n\t |***** boot_req_mode_pct            : %10d *****| \t",
        boot_req_mode_pct)};
    str = {str,  $sformatf("\n\t |***** auto_req_mode_pct            : %10d *****| \t",
        auto_req_mode_pct)};
    str = {str,  $sformatf("\n\t |***** MAX_NUM_ENDPOINTS            : %10d *****| \t",
        MAX_NUM_ENDPOINTS)};
    str = {str,  $sformatf("\n\t |***** min_num_boot_reqs            : %10d *****| \t",
        min_num_boot_reqs)};
    str = {str,  $sformatf("\n\t |***** max_num_boot_reqs            : %10d *****| \t",
        max_num_boot_reqs)};
    str = {str,  $sformatf("\n\t |***** force_disable_pct            : %10d *****| \t",
        force_disable_pct)};
    str = {str,  $sformatf("\n\t |*****************************************************| \t")};
    str = {str, "\n"};
    return str;
  endfunction

endclass
