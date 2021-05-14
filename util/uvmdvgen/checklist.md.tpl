---
title: "${name.upper()} Checklist"
---

<!--
NOTE: This is a template checklist document that is required to be copied over to the 'doc'
directory for a new design that transitions from L0 (Specification) to L1 (Development)
stage, and updated as needed. Once done, please remove this comment before checking it in.
-->
This checklist is for [Hardware Stage]({{< relref "/doc/project/development_stages.md" >}}) transitions for the [${name.upper()} peripheral.]({{< relref "." >}})
All checklist items refer to the content in the [Checklist.]({{< relref "/doc/project/checklist.md" >}})

<%text>## Design Checklist</%text>

<%text>### D1</%text>

Type          | Item                           | Resolution  | Note/Collaterals
--------------|--------------------------------|-------------|------------------
Documentation | [SPEC_COMPLETE][]              | Not Started | [${name.upper()} Design Spec]({{<relref "." >}})
Documentation | [CSR_DEFINED][]                | Not Started |
RTL           | [CLKRST_CONNECTED][]           | Not Started |
RTL           | [IP_TOP][]                     | Not Started |
RTL           | [IP_INSTANTIABLE][]            | Not Started |
RTL           | [PHYSICAL_MACROS_DEFINED_80][] | Not Started |
RTL           | [FUNC_IMPLEMENTED][]           | Not Started |
RTL           | [ASSERT_KNOWN_ADDED][]         | Not Started |
Code Quality  | [LINT_SETUP][]                 | Not Started |

[SPEC_COMPLETE]:              {{<relref "/doc/project/checklist.md#spec_complete" >}}
[CSR_DEFINED]:                {{<relref "/doc/project/checklist.md#csr_defined" >}}
[CLKRST_CONNECTED]:           {{<relref "/doc/project/checklist.md#clkrst_connected" >}}
[IP_TOP]:                     {{<relref "/doc/project/checklist.md#ip_top" >}}
[IP_INSTANTIABLE]:            {{<relref "/doc/project/checklist.md#ip_instantiable" >}}
[PHYSICAL_MACROS_DEFINED_80]: {{<relref "/doc/project/checklist.md#physical_macros_defined_80" >}}
[FUNC_IMPLEMENTED]:           {{<relref "/doc/project/checklist.md#func_implemented" >}}
[ASSERT_KNOWN_ADDED]:         {{<relref "/doc/project/checklist.md#assert_known_added" >}}
[LINT_SETUP]:                 {{<relref "/doc/project/checklist.md#lint_setup" >}}

<%text>### D2</%text>

Type          | Item                    | Resolution  | Note/Collaterals
--------------|-------------------------|-------------|------------------
Documentation | [NEW_FEATURES][]        | Not Started |
Documentation | [BLOCK_DIAGRAM][]       | Not Started |
Documentation | [DOC_INTERFACE][]       | Not Started |
Documentation | [MISSING_FUNC][]        | Not Started |
Documentation | [FEATURE_FROZEN][]      | Not Started |
RTL           | [FEATURE_COMPLETE][]    | Not Started |
RTL           | [AREA_CHECK][]          | Not Started |
RTL           | [PORT_FROZEN][]         | Not Started |
RTL           | [ARCHITECTURE_FROZEN][] | Not Started |
RTL           | [REVIEW_TODO][]         | Not Started |
RTL           | [STYLE_X][]             | Not Started |
Code Quality  | [LINT_PASS][]           | Not Started |
Code Quality  | [CDC_SETUP][]           | Not Started |
Code Quality  | [FPGA_TIMING][]         | Not Started |
Code Quality  | [CDC_SYNCMACRO][]       | Not Started |
Security      | [SEC_CM_IMPLEMENTED][]  | Not Started |
Security      | [SEC_NON_RESET_FLOPS][] | Not Started |
Security      | [SEC_SHADOW_REGS][]     | Not Started |
Security      | [SEC_RND_CNST][]        | Not Started |

[NEW_FEATURES]:        {{<relref "/doc/project/checklist.md#new_features" >}}
[BLOCK_DIAGRAM]:       {{<relref "/doc/project/checklist.md#block_diagram" >}}
[DOC_INTERFACE]:       {{<relref "/doc/project/checklist.md#doc_interface" >}}
[MISSING_FUNC]:        {{<relref "/doc/project/checklist.md#missing_func" >}}
[FEATURE_FROZEN]:      {{<relref "/doc/project/checklist.md#feature_frozen" >}}
[FEATURE_COMPLETE]:    {{<relref "/doc/project/checklist.md#feature_complete" >}}
[AREA_CHECK]:          {{<relref "/doc/project/checklist.md#area_check" >}}
[PORT_FROZEN]:         {{<relref "/doc/project/checklist.md#port_frozen" >}}
[ARCHITECTURE_FROZEN]: {{<relref "/doc/project/checklist.md#architecture_frozen" >}}
[REVIEW_TODO]:         {{<relref "/doc/project/checklist.md#review_todo" >}}
[STYLE_X]:             {{<relref "/doc/project/checklist.md#style_x" >}}
[LINT_PASS]:           {{<relref "/doc/project/checklist.md#lint_pass" >}}
[CDC_SETUP]:           {{<relref "/doc/project/checklist.md#cdc_setup" >}}
[FPGA_TIMING]:         {{<relref "/doc/project/checklist.md#fpga_timing" >}}
[CDC_SYNCMACRO]:       {{<relref "/doc/project/checklist.md#cdc_syncmacro" >}}
[SEC_CM_IMPLEMENTED]:  {{<relref "/doc/project/checklist.md#sec_cm_implemented" >}}
[SEC_NON_RESET_FLOPS]: {{<relref "/doc/project/checklist.md#sec_non_reset_flops" >}}
[SEC_SHADOW_REGS]:     {{<relref "/doc/project/checklist.md#sec_shadow_regs" >}}
[SEC_RND_CNST]:        {{<relref "/doc/project/checklist.md#sec_rnd_cnst" >}}

<%text>### D3</%text>

 Type         | Item                    | Resolution  | Note/Collaterals
--------------|-------------------------|-------------|------------------
Documentation | [NEW_FEATURES_D3][]     | Not Started |
RTL           | [TODO_COMPLETE][]       | Not Started |
Code Quality  | [LINT_COMPLETE][]       | Not Started |
Code Quality  | [CDC_COMPLETE][]        | Not Started |
Review        | [REVIEW_RTL][]          | Not Started |
Review        | [REVIEW_DELETED_FF][]   | Not Started |
Review        | [REVIEW_SW_CSR][]       | Not Started |
Review        | [REVIEW_SW_FATAL_ERR][] | Not Started |
Review        | [REVIEW_SW_CHANGE][]    | Not Started |
Review        | [REVIEW_SW_ERRATA][]    | Not Started |
Review        | Reviewer(s)             | Not Started |
Review        | Signoff date            | Not Started |

[NEW_FEATURES_D3]:      {{<relref "/doc/project/checklist.md#new_features_d3" >}}
[TODO_COMPLETE]:        {{<relref "/doc/project/checklist.md#todo_complete" >}}
[LINT_COMPLETE]:        {{<relref "/doc/project/checklist.md#lint_complete" >}}
[CDC_COMPLETE]:         {{<relref "/doc/project/checklist.md#cdc_complete" >}}
[REVIEW_RTL]:           {{<relref "/doc/project/checklist.md#review_rtl" >}}
[REVIEW_DBG]:           {{<relref "/doc/project/checklist.md#review_dbg" >}}
[REVIEW_DELETED_FF]:    {{<relref "/doc/project/checklist.md#review_deleted_ff" >}}
[REVIEW_SW_CSR]:        {{<relref "/doc/project/checklist.md#review_sw_csr" >}}
[REVIEW_SW_FATAL_ERR]:  {{<relref "/doc/project/checklist.md#review_sw_fatal_err" >}}
[REVIEW_SW_CHANGE]:     {{<relref "/doc/project/checklist.md#review_sw_change" >}}
[REVIEW_SW_ERRATA]:     {{<relref "/doc/project/checklist.md#review_sw_errata" >}}

<%text>## Verification Checklist</%text>

<%text>### V1</%text>

 Type         | Item                                  | Resolution  | Note/Collaterals
--------------|---------------------------------------|-------------|------------------
Documentation | [DV_DOC_DRAFT_COMPLETED][]            | Not Started | [${name.upper()} DV document]({{<relref "dv" >}})
Documentation | [TESTPLAN_COMPLETED][]                | Not Started | [${name.upper()} Testplan]({{<relref "dv/index.md#testplan" >}})
Testbench     | [TB_TOP_CREATED][]                    | Not Started |
Testbench     | [PRELIMINARY_ASSERTION_CHECKS_ADDED][]| Not Started |
Testbench     | [SIM_TB_ENV_CREATED][]                | Not Started |
Testbench     | [SIM_RAL_MODEL_GEN_AUTOMATED][]       | Not Started |
Testbench     | [CSR_CHECK_GEN_AUTOMATED][]           | Not Started |
Testbench     | [TB_GEN_AUTOMATED][]                  | Not Started |
Tests         | [SIM_SMOKE_TEST_PASSING][]            | Not Started |
Tests         | [SIM_CSR_MEM_TEST_SUITE_PASSING][]    | Not Started |
Tests         | [FPV_MAIN_ASSERTIONS_PROVEN][]        | Not Started |
Tool Setup    | [SIM_ALT_TOOL_SETUP][]                | Not Started |
Regression    | [SIM_SMOKE_REGRESSION_SETUP][]        | Not Started |
Regression    | [SIM_NIGHTLY_REGRESSION_SETUP][]      | Not Started |
Regression    | [FPV_REGRESSION_SETUP][]              | Not Started |
Coverage      | [SIM_COVERAGE_MODEL_ADDED][]          | Not Started |
Code Quality  | [TB_LINT_SETUP][]                     | Not Started |
Integration   | [PRE_VERIFIED_SUB_MODULES_V1][]       | Not Started |
Review        | [DESIGN_SPEC_REVIEWED][]              | Not Started |
Review        | [TESTPLAN_REVIEWED][]                 | Not Started |
Review        | [STD_TEST_CATEGORIES_PLANNED][]       | Not Started | Exception (?)
Review        | [V2_CHECKLIST_SCOPED][]               | Not Started |

[DV_DOC_DRAFT_COMPLETED]:             {{<relref "/doc/project/checklist.md#dv_doc_draft_completed" >}}
[TESTPLAN_COMPLETED]:                 {{<relref "/doc/project/checklist.md#testplan_completed" >}}
[TB_TOP_CREATED]:                     {{<relref "/doc/project/checklist.md#tb_top_created" >}}
[PRELIMINARY_ASSERTION_CHECKS_ADDED]: {{<relref "/doc/project/checklist.md#preliminary_assertion_checks_added" >}}
[SIM_TB_ENV_CREATED]:                 {{<relref "/doc/project/checklist.md#sim_tb_env_created" >}}
[SIM_RAL_MODEL_GEN_AUTOMATED]:        {{<relref "/doc/project/checklist.md#sim_ral_model_gen_automated" >}}
[CSR_CHECK_GEN_AUTOMATED]:            {{<relref "/doc/project/checklist.md#csr_check_gen_automated" >}}
[TB_GEN_AUTOMATED]:                   {{<relref "/doc/project/checklist.md#tb_gen_automated" >}}
[SIM_SMOKE_TEST_PASSING]:             {{<relref "/doc/project/checklist.md#sim_smoke_test_passing" >}}
[SIM_CSR_MEM_TEST_SUITE_PASSING]:     {{<relref "/doc/project/checklist.md#sim_csr_mem_test_suite_passing" >}}
[FPV_MAIN_ASSERTIONS_PROVEN]:         {{<relref "/doc/project/checklist.md#fpv_main_assertions_proven" >}}
[SIM_ALT_TOOL_SETUP]:                 {{<relref "/doc/project/checklist.md#sim_alt_tool_setup" >}}
[SIM_SMOKE_REGRESSION_SETUP]:         {{<relref "/doc/project/checklist.md#sim_smoke_regression_setup" >}}
[SIM_NIGHTLY_REGRESSION_SETUP]:       {{<relref "/doc/project/checklist.md#sim_nightly_regression_setup" >}}
[FPV_REGRESSION_SETUP]:               {{<relref "/doc/project/checklist.md#fpv_regression_setup" >}}
[SIM_COVERAGE_MODEL_ADDED]:           {{<relref "/doc/project/checklist.md#sim_coverage_model_added" >}}
[TB_LINT_SETUP]:                      {{<relref "/doc/project/checklist.md#tb_lint_setup" >}}
[PRE_VERIFIED_SUB_MODULES_V1]:        {{<relref "/doc/project/checklist.md#pre_verified_sub_modules_v1" >}}
[DESIGN_SPEC_REVIEWED]:               {{<relref "/doc/project/checklist.md#design_spec_reviewed" >}}
[TESTPLAN_REVIEWED]:                  {{<relref "/doc/project/checklist.md#testplan_reviewed" >}}
[STD_TEST_CATEGORIES_PLANNED]:        {{<relref "/doc/project/checklist.md#std_test_categories_planned" >}}
[V2_CHECKLIST_SCOPED]:                {{<relref "/doc/project/checklist.md#v2_checklist_scoped" >}}

<%text>### V2</%text>

 Type         | Item                                    | Resolution  | Note/Collaterals
--------------|-----------------------------------------|-------------|------------------
Documentation | [DESIGN_DELTAS_CAPTURED_V2][]           | Not Started |
Documentation | [DV_DOC_COMPLETED][]                    | Not Started |
Testbench     | [FUNCTIONAL_COVERAGE_IMPLEMENTED][]     | Not Started |
Testbench     | [ALL_INTERFACES_EXERCISED][]            | Not Started |
Testbench     | [ALL_ASSERTION_CHECKS_ADDED][]          | Not Started |
Testbench     | [SIM_TB_ENV_COMPLETED][]                | Not Started |
Tests         | [SIM_ALL_TESTS_PASSING][]               | Not Started |
Tests         | [FPV_ALL_ASSERTIONS_WRITTEN][]          | Not Started |
Tests         | [FPV_ALL_ASSUMPTIONS_REVIEWED][]        | Not Started |
Tests         | [SIM_FW_SIMULATED][]                    | Not Started |
Regression    | [SIM_NIGHTLY_REGRESSION_V2][]           | Not Started |
Coverage      | [SIM_CODE_COVERAGE_V2][]                | Not Started |
Coverage      | [SIM_FUNCTIONAL_COVERAGE_V2][]          | Not Started |
Coverage      | [FPV_CODE_COVERAGE_V2][]                | Not Started |
Coverage      | [FPV_COI_COVERAGE_V2][]                 | Not Started |
Code Quality  | [TB_LINT_PASS][]                        | Not Started |
Integration   | [PRE_VERIFIED_SUB_MODULES_V2][]         | Not Started |
Issues        | [NO_HIGH_PRIORITY_ISSUES_PENDING][]     | Not Started |
Issues        | [ALL_LOW_PRIORITY_ISSUES_ROOT_CAUSED][] | Not Started |
Review        | [DV_DOC_TESTPLAN_REVIEWED][]            | Not Started |
Review        | [V3_CHECKLIST_SCOPED][]                 | Not Started |

[DESIGN_DELTAS_CAPTURED_V2]:          {{<relref "/doc/project/checklist.md#design_deltas_captured_v2" >}}
[DV_DOC_COMPLETED]:                   {{<relref "/doc/project/checklist.md#dv_doc_completed" >}}
[FUNCTIONAL_COVERAGE_IMPLEMENTED]:    {{<relref "/doc/project/checklist.md#functional_coverage_implemented" >}}
[ALL_INTERFACES_EXERCISED]:           {{<relref "/doc/project/checklist.md#all_interfaces_exercised" >}}
[ALL_ASSERTION_CHECKS_ADDED]:         {{<relref "/doc/project/checklist.md#all_assertion_checks_added" >}}
[SIM_TB_ENV_COMPLETED]:               {{<relref "/doc/project/checklist.md#sim_tb_env_completed" >}}
[SIM_ALL_TESTS_PASSING]:              {{<relref "/doc/project/checklist.md#sim_all_tests_passing" >}}
[FPV_ALL_ASSERTIONS_WRITTEN]:         {{<relref "/doc/project/checklist.md#fpv_all_assertions_written" >}}
[FPV_ALL_ASSUMPTIONS_REVIEWED]:       {{<relref "/doc/project/checklist.md#fpv_all_assumptions_reviewed" >}}
[SIM_FW_SIMULATED]:                   {{<relref "/doc/project/checklist.md#sim_fw_simulated" >}}
[SIM_NIGHTLY_REGRESSION_V2]:          {{<relref "/doc/project/checklist.md#sim_nightly_regression_v2" >}}
[SIM_CODE_COVERAGE_V2]:               {{<relref "/doc/project/checklist.md#sim_code_coverage_v2" >}}
[SIM_FUNCTIONAL_COVERAGE_V2]:         {{<relref "/doc/project/checklist.md#sim_functional_coverage_v2" >}}
[FPV_CODE_COVERAGE_V2]:               {{<relref "/doc/project/checklist.md#fpv_code_coverage_v2" >}}
[FPV_COI_COVERAGE_V2]:                {{<relref "/doc/project/checklist.md#fpv_coi_coverage_v2" >}}
[TB_LINT_PASS]:                       {{<relref "/doc/project/checklist.md#tb_lint_pass" >}}
[PRE_VERIFIED_SUB_MODULES_V2]:        {{<relref "/doc/project/checklist.md#pre_verified_sub_modules_v2" >}}
[NO_HIGH_PRIORITY_ISSUES_PENDING]:    {{<relref "/doc/project/checklist.md#no_high_priority_issues_pending" >}}
[ALL_LOW_PRIORITY_ISSUES_ROOT_CAUSED]:{{<relref "/doc/project/checklist.md#all_low_priority_issues_root_caused" >}}
[DV_DOC_TESTPLAN_REVIEWED]:           {{<relref "/doc/project/checklist.md#dv_doc_testplan_reviewed" >}}
[V3_CHECKLIST_SCOPED]:                {{<relref "/doc/project/checklist.md#v3_checklist_scoped" >}}

<%text>### V3</%text>

 Type         | Item                              | Resolution  | Note/Collaterals
--------------|-----------------------------------|-------------|------------------
Documentation | [DESIGN_DELTAS_CAPTURED_V3][]     | Not Started |
Tests         | [X_PROP_ANALYSIS_COMPLETED][]     | Not Started |
Tests         | [FPV_ASSERTIONS_PROVEN_AT_V3][]   | Not Started |
Regression    | [SIM_NIGHTLY_REGRESSION_AT_V3][]  | Not Started |
Coverage      | [SIM_CODE_COVERAGE_AT_100][]      | Not Started |
Coverage      | [SIM_FUNCTIONAL_COVERAGE_AT_100][]| Not Started |
Coverage      | [FPV_CODE_COVERAGE_AT_100][]      | Not Started |
Coverage      | [FPV_COI_COVERAGE_AT_100][]       | Not Started |
Code Quality  | [ALL_TODOS_RESOLVED][]            | Not Started |
Code Quality  | [NO_TOOL_WARNINGS_THROWN][]       | Not Started |
Code Quality  | [TB_LINT_COMPLETE][]              | Not Started |
Integration   | [PRE_VERIFIED_SUB_MODULES_V3][]   | Not Started |
Issues        | [NO_ISSUES_PENDING][]             | Not Started |
Review        | Reviewer(s)                       | Not Started |
Review        | Signoff date                      | Not Started |

[DESIGN_DELTAS_CAPTURED_V3]:     {{<relref "/doc/project/checklist.md#design_deltas_captured_v3" >}}
[X_PROP_ANALYSIS_COMPLETED]:     {{<relref "/doc/project/checklist.md#x_prop_analysis_completed" >}}
[FPV_ASSERTIONS_PROVEN_AT_V3]:   {{<relref "/doc/project/checklist.md#fpv_assertions_proven_at_v3" >}}
[SIM_NIGHTLY_REGRESSION_AT_V3]:  {{<relref "/doc/project/checklist.md#sim_nightly_regression_at_v3" >}}
[SIM_CODE_COVERAGE_AT_100]:      {{<relref "/doc/project/checklist.md#sim_code_coverage_at_100" >}}
[SIM_FUNCTIONAL_COVERAGE_AT_100]:{{<relref "/doc/project/checklist.md#sim_functional_coverage_at_100" >}}
[FPV_CODE_COVERAGE_AT_100]:      {{<relref "/doc/project/checklist.md#fpv_code_coverage_at_100" >}}
[FPV_COI_COVERAGE_AT_100]:       {{<relref "/doc/project/checklist.md#fpv_coi_coverage_at_100" >}}
[ALL_TODOS_RESOLVED]:            {{<relref "/doc/project/checklist.md#all_todos_resolved" >}}
[NO_TOOL_WARNINGS_THROWN]:       {{<relref "/doc/project/checklist.md#no_tool_warnings_thrown" >}}
[TB_LINT_COMPLETE]:              {{<relref "/doc/project/checklist.md#tb_lint_complete" >}}
[PRE_VERIFIED_SUB_MODULES_V3]:   {{<relref "/doc/project/checklist.md#pre_verified_sub_modules_v3" >}}
[NO_ISSUES_PENDING]:             {{<relref "/doc/project/checklist.md#no_issues_pending" >}}
