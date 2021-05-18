---
title: "UART Checklist"
---

This checklist is for [Hardware Stage][] transitions for the [UART peripheral.](../)
All checklist items refer to the content in the [Checklist.]({{<relref "/doc/project/checklist.md">}})

[Hardware Stage]: {{<relref "/doc/project/development_stages.md" >}}


## Design Checklist

### D1

Type          | Item                           | Resolution  | Note/Collaterals
--------------|--------------------------------|-------------|------------------
Documentation | [SPEC_COMPLETE][]              | Done        | [UART Spec](../)
Documentation | [CSR_DEFINED][]                | Done        |
RTL           | [CLKRST_CONNECTED][]           | Done        |
RTL           | [IP_TOP][]                     | Done        |
RTL           | [IP_INSTANTIABLE][]            | Done        |
RTL           | [PHYSICAL_MACROS_DEFINED_80][] | N/A         |
RTL           | [FUNC_IMPLEMENTED][]           | Done        |
RTL           | [ASSERT_KNOWN_ADDED][]         | Done        |
Code Quality  | [LINT_SETUP][]                 | Done        |


[SPEC_COMPLETE]:              {{<relref "/doc/project/checklist.md#spec_complete" >}}
[CSR_DEFINED]:                {{<relref "/doc/project/checklist.md#csr_defined" >}}
[CLKRST_CONNECTED]:           {{<relref "/doc/project/checklist.md#clkrst_connected" >}}
[IP_TOP]:                     {{<relref "/doc/project/checklist.md#ip_top" >}}
[IP_INSTANTIABLE]:            {{<relref "/doc/project/checklist.md#ip_instantiable" >}}
[PHYSICAL_MACROS_DEFINED_80]: {{<relref "/doc/project/checklist.md#physical_macros_defined_80" >}}
[FUNC_IMPLEMENTED]:           {{<relref "/doc/project/checklist.md#func_implemented" >}}
[ASSERT_KNOWN_ADDED]:         {{<relref "/doc/project/checklist.md#assert_known_added" >}}
[LINT_SETUP]:                 {{<relref "/doc/project/checklist.md#lint_setup" >}}

### D1 Exceptions

[PHYSICAL_MACROS_DEFINED_80][] is waived as UART doesn't have memories inside.

### D2

Type          | Item                    | Resolution  | Note/Collaterals
--------------|-------------------------|-------------|------------------
Documentation | [NEW_FEATURES][]        | N/A         |
Documentation | [BLOCK_DIAGRAM][]       | N/A         |
Documentation | [DOC_INTERFACE][]       | Done        |
Documentation | [MISSING_FUNC][]        | N/A         |
Documentation | [FEATURE_FROZEN][]      | Done        |
RTL           | [FEATURE_COMPLETE][]    | Done        |
RTL           | [AREA_CHECK][]          | Done        | Area Check Done (on FPGA)
RTL           | [PORT_FROZEN][]         | Done        |
RTL           | [ARCHITECTURE_FROZEN][] | Done        |
RTL           | [REVIEW_TODO][]         | Done        |
RTL           | [STYLE_X][]             | N/A         | No assignment of X
Code Quality  | [LINT_PASS][]           | Done        | Lint waivers reviewed
Code Quality  | [CDC_SETUP][]           | N/A         | No CDC path
Code Quality  | [FPGA_TIMING][]         | Done        | Fmax 50MHz on NexysVideo
Code Quality  | [CDC_SYNCMACRO][]       | N/A         |
Security      | [SEC_CM_IMPLEMENTED][]  | N/A         |
Security      | [SEC_NON_RESET_FLOPS][] | N/A         |
Security      | [SEC_SHADOW_REGS][]     | N/A         |
Security      | [SEC_RND_CNST][]        | N/A         |

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

### D3

 Type         | Item                    | Resolution  | Note/Collaterals
--------------|-------------------------|-------------|------------------
Documentation | [NEW_FEATURES_D3][]     | N/A         |
RTL           | [TODO_COMPLETE][]       | Done        |
Code Quality  | [LINT_COMPLETE][]       | Done        |
Code Quality  | [CDC_COMPLETE][]        | N/A         |
Review        | [REVIEW_RTL][]          | Done        | by @msfschaffner
Review        | [REVIEW_DELETED_FF][]   | N/A         | Not reported by FPGA (@eunchan double-check)
Review        | [REVIEW_SW_CSR][]       | Done        |
Review        | [REVIEW_SW_FATAL_ERR][] | Done        | by @moidx
Review        | [REVIEW_SW_CHANGE][]    | N/A         |
Review        | [REVIEW_SW_ERRATA][]    | Done        |
Review        | Reviewer(s)             | Done        | @weicaiyang @sjgitty @msfschaffner
Review        | Signoff date            | Done        | 2019-10-31

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

## Verification Checklist

### V1

 Type         | Item                                  | Resolution  | Note/Collaterals
--------------|---------------------------------------|-------------|------------------
Documentation | [DV_DOC_DRAFT_COMPLETED][]            | Done        | [UART DV document]({{<relref "dv/index.md" >}})
Documentation | [TESTPLAN_COMPLETED][]                | Done        | [UART Testplan]({{<relref "dv/index.md#testplan" >}})
Testbench     | [TB_TOP_CREATED][]                    | Done        |
Testbench     | [PRELIMINARY_ASSERTION_CHECKS_ADDED][]| Done        |
Testbench     | [SIM_TB_ENV_CREATED][]                | Done        |
Testbench     | [SIM_RAL_MODEL_GEN_AUTOMATED][]       | Done        |
Testbench     | [CSR_CHECK_GEN_AUTOMATED][]           | waived      | Revisit later. Tool setup in progress.
Testbench     | [TB_GEN_AUTOMATED][]                  | N/A         |
Tests         | [SIM_SMOKE_TEST_PASSING][]            | Done        |
Tests         | [SIM_CSR_MEM_TEST_SUITE_PASSING][]    | Done        |
Tests         | [FPV_MAIN_ASSERTIONS_PROVEN][]        | N/A         |
Tool Setup    | [SIM_ALT_TOOL_SETUP][]                | Done        |
Regression    | [SIM_SMOKE_REGRESSION_SETUP][]        | Done        | Exception (implemented in local)
Regression    | [SIM_NIGHTLY_REGRESSION_SETUP][]      | Done        | Exception (implemented in local)
Regression    | [FPV_REGRESSION_SETUP][]              | N/A         |
Coverage      | [SIM_COVERAGE_MODEL_ADDED][]          | Done        |
Code Quality  | [TB_LINT_SETUP][]                     | Done        |
Integration   | [PRE_VERIFIED_SUB_MODULES_V1][]       | N/A         | Except for IP module
Review        | [DESIGN_SPEC_REVIEWED][]              | Done        |
Review        | [TESTPLAN_REVIEWED][]                 | Done        |
Review        | [STD_TEST_CATEGORIES_PLANNED][]       | Done        | Exception (Security, Power, Debug)
Review        | [V2_CHECKLIST_SCOPED][]               | Done        |

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

### V2

 Type         | Item                                    | Resolution  | Note/Collaterals
--------------|-----------------------------------------|-------------|------------------
Documentation | [DESIGN_DELTAS_CAPTURED_V2][]           | N/A         |
Documentation | [DV_DOC_COMPLETED][]                    | Done        |
Testbench     | [FUNCTIONAL_COVERAGE_IMPLEMENTED][]     | Not Started |
Testbench     | [ALL_INTERFACES_EXERCISED][]            | Done        |
Testbench     | [ALL_ASSERTION_CHECKS_ADDED][]          | Done        |
Testbench     | [SIM_TB_ENV_COMPLETED][]                | Done        |
Tests         | [SIM_ALL_TESTS_PASSING][]               | Done        |
Tests         | [FPV_ALL_ASSERTIONS_WRITTEN][]          | N/A         |
Tests         | [FPV_ALL_ASSUMPTIONS_REVIEWED][]        | N/A         |
Tests         | [SIM_FW_SIMULATED][]                    | N/A         |
Regression    | [SIM_NIGHTLY_REGRESSION_V2][]           | Done        |
Coverage      | [SIM_CODE_COVERAGE_V2][]                | Done        |
Coverage      | [SIM_FUNCTIONAL_COVERAGE_V2][]          | Done        |
Coverage      | [FPV_CODE_COVERAGE_V2][]                | N/A         |
Coverage      | [FPV_COI_COVERAGE_V2][]                 | N/A         |
Code Quality  | [TB_LINT_PASS][]                        | Done        |
Issues        | [NO_HIGH_PRIORITY_ISSUES_PENDING][]     | Done        |
Issues        | [ALL_LOW_PRIORITY_ISSUES_ROOT_CAUSED][] | Done        |
Integration   | [PRE_VERIFIED_SUB_MODULES_V2][]         | N/A         |
Review        | [DV_DOC_TESTPLAN_REVIEWED][]            | Not Started |
Review        | [V3_CHECKLIST_SCOPED][]                 | Done        |

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

### V3

 Type         | Item                              | Resolution  | Note/Collaterals
--------------|-----------------------------------|-------------|------------------
Documentation | [DESIGN_DELTAS_CAPTURED_V3][]     | N/A         |
Tests         | [X_PROP_ANALYSIS_COMPLETED][]     | Waived      | Revisit later. Tool setup in progress
Tests         | [FPV_ASSERTIONS_PROVEN_AT_V3][]   | N/A         |
Regression    | [SIM_NIGHTLY_REGRESSION_AT_V3][]  | Done        |
Coverage      | [SIM_CODE_COVERAGE_AT_100][]      | Done        |[common_cov_excl.el][], [uart_cov_excl.el][]
Coverage      | [SIM_FUNCTIONAL_COVERAGE_AT_100][]| Done        |
Coverage      | [FPV_CODE_COVERAGE_AT_100][]      | N/A         |
Coverage      | [FPV_COI_COVERAGE_AT_100][]       | N/A         |
Code Quality  | [ALL_TODOS_RESOLVED][]            | Done        |
Code Quality  | [NO_TOOL_WARNINGS_THROWN][]       | Done        |
Code Quality  | [TB_LINT_COMPLETE][]              | Not Started |
Integration   | [PRE_VERIFIED_SUB_MODULES_V3][]   | N/A         |
Issues        | [NO_ISSUES_PENDING][]             | Done        |
Review        | Reviewer(s)                       | Done        | @eunchan @sjgitty @sriyerg
Review        | Signoff date                      | Done        | 2019-11-01

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

[common_cov_excl.el]:https://github.com/lowRISC/opentitan/blob/master/hw/dv/tools/vcs/common_cov_excl.el
[uart_cov_excl.el]:  https://github.com/lowRISC/opentitan/blob/04bb36e0ae1430262b048d400102b0fed43377ac/hw/ip/uart/dv/cov/uart_cov_excl.el
