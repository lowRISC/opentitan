---
title: "TL-UL Checklist"
---

This checklist is for [Hardware Stage]({{< relref "/doc/project/development_stages.md" >}}) transitions for the [TL-UL component.]({{<relref "/hw/ip/tlul/doc">}})
All checklist items refer to the content in the [Checklist]({{< relref "/doc/project/checklist.md" >}}).

## Design Checklist

### D1

Type          | Item                           | Resolution  | Note/Collaterals
--------------|--------------------------------|-------------|------------------
Documentation | [SPEC_COMPLETE][]              | Done        | [TL-UL Spec][] [crossbar_tool][]
Documentation | [CSR_DEFINED][]                | N/A         |
RTL           | [CLKRST_CONNECTED][]           | Done        |
RTL           | [IP_TOP][]                     | Done        |
RTL           | [IP_INSTANTIABLE][]            | Done        |
RTL           | [PHYSICAL_MACROS_DEFINED_80][] | N/A         |
RTL           | [FUNC_IMPLEMENTED][]           | Done        |
RTL           | [ASSERT_KNOWN_ADDED][]         | Done        |
Code Quality  | [LINT_SETUP][]                 | Done        |

[TL-UL Spec]:         {{<relref "/hw/ip/tlul/doc">}}
[crossbar_tool]:      {{<relref "/doc/rm/crossbar_tool">}}

[SPEC_COMPLETE]:              {{<relref "/doc/project/checklist.md#spec_complete" >}}
[CSR_DEFINED]:                {{<relref "/doc/project/checklist.md#csr_defined" >}}
[CLKRST_CONNECTED]:           {{<relref "/doc/project/checklist.md#clkrst_connected" >}}
[IP_TOP]:                     {{<relref "/doc/project/checklist.md#ip_top" >}}
[IP_INSTANTIABLE]:            {{<relref "/doc/project/checklist.md#ip_instantiable" >}}
[PHYSICAL_MACROS_DEFINED_80]: {{<relref "/doc/project/checklist.md#physical_macros_defined_80" >}}
[FUNC_IMPLEMENTED]:           {{<relref "/doc/project/checklist.md#func_implemented" >}}
[ASSERT_KNOWN_ADDED]:         {{<relref "/doc/project/checklist.md#assert_known_added" >}}
[LINT_SETUP]:                 {{<relref "/doc/project/checklist.md#lint_setup" >}}

### D2

Type          | Item                      | Resolution  | Note/Collaterals
--------------|---------------------------|-------------|------------------
Documentation | [NEW_FEATURES][]          | N/A         |
Documentation | [BLOCK_DIAGRAM][]         | Done        |
Documentation | [DOC_INTERFACE][]         | N/A         |
Documentation | [DOC_INTEGRATION_GUIDE][] | Waived      | This checklist item has been added retrospectively.
Documentation | [MISSING_FUNC][]          | N/A         |
Documentation | [FEATURE_FROZEN][]        | Done        |
RTL           | [FEATURE_COMPLETE][]      | Done        |
RTL           | [PORT_FROZEN][]           | Done        | Targetting for current top_earlgrey( Port can be changed later based on top_earlgrey config)
RTL           | [ARCHITECTURE_FROZEN][]   | Done        |
RTL           | [REVIEW_TODO][]           | Done        | PR [#837][] is pending
RTL           | [STYLE_X][]               | Done        |
RTL           | [CDC_SYNCMACRO][]         | N/A         |
Code Quality  | [LINT_PASS][]             | Done        |
Code Quality  | [CDC_SETUP][]             | Waived      | No block-level flow available - waived to top-level signoff.
Code Quality  | [RDC_SETUP][]             | Waived      | No block-level flow available - waived to top-level signoff.
Code Quality  | [AREA_CHECK][]            | Done        |
Code Quality  | [TIMING_CHECK][]          | Done        | Pipeline inserted in front of Core IBEX. meet timing @ 50MHz on NexysVideo
Security      | [SEC_CM_DOCUMENTED][]     | N/A         |

[#837]: https://github.com/lowRISC/opentitan/pull/837

[NEW_FEATURES]:          {{<relref "/doc/project/checklist.md#new_features" >}}
[BLOCK_DIAGRAM]:         {{<relref "/doc/project/checklist.md#block_diagram" >}}
[DOC_INTERFACE]:         {{<relref "/doc/project/checklist.md#doc_interface" >}}
[DOC_INTEGRATION_GUIDE]: {{<relref "/doc/project/checklist.md#doc_integration_guide" >}}
[MISSING_FUNC]:          {{<relref "/doc/project/checklist.md#missing_func" >}}
[FEATURE_FROZEN]:        {{<relref "/doc/project/checklist.md#feature_frozen" >}}
[FEATURE_COMPLETE]:      {{<relref "/doc/project/checklist.md#feature_complete" >}}
[PORT_FROZEN]:           {{<relref "/doc/project/checklist.md#port_frozen" >}}
[ARCHITECTURE_FROZEN]:   {{<relref "/doc/project/checklist.md#architecture_frozen" >}}
[REVIEW_TODO]:           {{<relref "/doc/project/checklist.md#review_todo" >}}
[STYLE_X]:               {{<relref "/doc/project/checklist.md#style_x" >}}
[CDC_SYNCMACRO]:         {{<relref "/doc/project/checklist.md#cdc_syncmacro" >}}
[LINT_PASS]:             {{<relref "/doc/project/checklist.md#lint_pass" >}}
[CDC_SETUP]:             {{<relref "/doc/project/checklist.md#cdc_setup" >}}
[RDC_SETUP]:             {{<relref "/doc/project/checklist.md#rdc_setup" >}}
[AREA_CHECK]:            {{<relref "/doc/project/checklist.md#area_check" >}}
[TIMING_CHECK]:          {{<relref "/doc/project/checklist.md#timing_check" >}}
[SEC_CM_DOCUMENTED]:     {{<relref "/doc/project/checklist.md#sec_cm_documented" >}}

### D2S

 Type         | Item                         | Resolution  | Note/Collaterals
--------------|------------------------------|-------------|------------------
Security      | [SEC_CM_ASSETS_LISTED][]     | Not Started |
Security      | [SEC_CM_IMPLEMENTED][]       | Not Started |
Security      | [SEC_CM_RND_CNST][]          | Not Started |
Security      | [SEC_CM_NON_RESET_FLOPS][]   | Not Started |
Security      | [SEC_CM_SHADOW_REGS][]       | Not Started |
Security      | [SEC_CM_RTL_REVIEWED][]      | Not Started |
Security      | [SEC_CM_COUNCIL_REVIEWED][]  | Not Started |

[SEC_CM_ASSETS_LISTED]:    {{<relref "/doc/project/checklist.md#sec_cm_assets_listed" >}}
[SEC_CM_IMPLEMENTED]:      {{<relref "/doc/project/checklist.md#sec_cm_implemented" >}}
[SEC_CM_RND_CNST]:         {{<relref "/doc/project/checklist.md#sec_cm_rnd_cnst" >}}
[SEC_CM_NON_RESET_FLOPS]:  {{<relref "/doc/project/checklist.md#sec_cm_non_reset_flops" >}}
[SEC_CM_SHADOW_REGS]:      {{<relref "/doc/project/checklist.md#sec_cm_shadow_regs" >}}
[SEC_CM_RTL_REVIEWED]:     {{<relref "/doc/project/checklist.md#sec_cm_rtl_reviewed" >}}
[SEC_CM_COUNCIL_REVIEWED]: {{<relref "/doc/project/checklist.md#sec_cm_council_reviewed" >}}

### D3

 Type         | Item                    | Resolution  | Note/Collaterals
--------------|-------------------------|-------------|------------------
Documentation | [NEW_FEATURES_D3][]     | N/A         |
RTL           | [TODO_COMPLETE][]       | Done        | Resolved: [#837][]
Code Quality  | [LINT_COMPLETE][]       | Done        |
Code Quality  | [CDC_COMPLETE][]        | N/A         |
Code Quality  | [RDC_COMPLETE][]        | Not Started |
Review        | [REVIEW_RTL][]          | Done        | 1st @tjaychen / 2nd @martin-lueker
Review        | [REVIEW_DELETED_FF][]   | N/A         |
Review        | [REVIEW_SW_CHANGE][]    | N/A         |
Review        | [REVIEW_SW_ERRATA][]    | Done        |
Review        | Reviewer(s)             | Done        | @weicaiyang @tjaychen
Review        | Signoff date            | Done        | 2019-11-07

[NEW_FEATURES_D3]:      {{<relref "/doc/project/checklist.md#new_features_d3" >}}
[TODO_COMPLETE]:        {{<relref "/doc/project/checklist.md#todo_complete" >}}
[LINT_COMPLETE]:        {{<relref "/doc/project/checklist.md#lint_complete" >}}
[CDC_COMPLETE]:         {{<relref "/doc/project/checklist.md#cdc_complete" >}}
[RDC_COMPLETE]:         {{<relref "/doc/project/checklist.md#rdc_complete" >}}
[REVIEW_RTL]:           {{<relref "/doc/project/checklist.md#review_rtl" >}}
[REVIEW_DELETED_FF]:    {{<relref "/doc/project/checklist.md#review_deleted_ff" >}}
[REVIEW_SW_CHANGE]:     {{<relref "/doc/project/checklist.md#review_sw_change" >}}
[REVIEW_SW_ERRATA]:     {{<relref "/doc/project/checklist.md#review_sw_errata" >}}

## Verification Checklist

### V1

 Type         | Item                                  | Resolution  | Note/Collaterals
--------------|---------------------------------------|-------------|------------------
Documentation | [DV_DOC_DRAFT_COMPLETED][]            | Done        | [XBAR DV document][]
Documentation | [TESTPLAN_COMPLETED][]                | Done        | [XBAR Testplan][]
Testbench     | [TB_TOP_CREATED][]                    | Done        |
Testbench     | [PRELIMINARY_ASSERTION_CHECKS_ADDED][]| Done        |
Testbench     | [TB_ENV_CREATED][]                    | Done        |
Testbench     | [RAL_MODEL_GEN_AUTOMATED][]           | N/A         |
Testbench     | [TB_GEN_AUTOMATED][]                  | Waived      | Manually generated. Planned to automate later
Tests         | [SMOKE_TEST_PASSING][]                | Done        |
Tests         | [CSR_MEM_TEST_SUITE_PASSING][]        | N/A         |
Tool Setup    | [ALT_TOOL_SETUP][]                    | Done        |
Regression    | [SMOKE_REGRESSION_SETUP][]            | Done        | Exception (Runs at local)
Regression    | [NIGHTLY_REGRESSION_SETUP][]          | Done        | Exception (Runs at local)
Coverage      | [COVERAGE_MODEL_ADDED][]              | Done        |
Code Quality  | [TB_LINT_SETUP][]                     | Done        |
Integration   | [PRE_VERIFIED_SUB_MODULES_V1][]       | Waived      | prim_arbiter to be verified later
Review        | [DESIGN_SPEC_REVIEWED][]              | Done        |
Review        | [TESTPLAN_REVIEWED][]                 | Done        |
Review        | [STD_TEST_CATEGORIES_PLANNED][]       | Done        | Exception (Security, Power, Debug, Performance)
Review        | [V2_CHECKLIST_SCOPED][]               | Done        |

[XBAR DV document]:                   {{<relref "/hw/ip/tlul/doc/dv">}}
[XBAR Testplan]:                      {{<relref "/hw/ip/tlul/doc/dv/index.md#testplan">}}

[DV_DOC_DRAFT_COMPLETED]:             {{<relref "/doc/project/checklist.md#dv-doc-draft-completed" >}}
[TESTPLAN_COMPLETED]:                 {{<relref "/doc/project/checklist.md#testplan-completed" >}}
[TB_TOP_CREATED]:                     {{<relref "/doc/project/checklist.md#tb-top-created" >}}
[PRELIMINARY_ASSERTION_CHECKS_ADDED]: {{<relref "/doc/project/checklist.md#preliminary-assertion-checks-added" >}}
[TB_ENV_CREATED]:                     {{<relref "/doc/project/checklist.md#tb-env-created" >}}
[RAL_MODEL_GEN_AUTOMATED]:            {{<relref "/doc/project/checklist.md#ral-model-gen-automated" >}}
[TB_GEN_AUTOMATED]:                   {{<relref "/doc/project/checklist.md#tb-gen-automated" >}}
[SMOKE_TEST_PASSING]:                 {{<relref "/doc/project/checklist.md#smoke-test-passing" >}}
[CSR_MEM_TEST_SUITE_PASSING]:         {{<relref "/doc/project/checklist.md#csr-mem-test-suite-passing" >}}
[ALT_TOOL_SETUP]:                     {{<relref "/doc/project/checklist.md#alt-tool-setup" >}}
[SMOKE_REGRESSION_SETUP]:             {{<relref "/doc/project/checklist.md#smoke-regression-setup" >}}
[NIGHTLY_REGRESSION_SETUP]:           {{<relref "/doc/project/checklist.md#nightly-regression-setup" >}}
[COVERAGE_MODEL_ADDED]:               {{<relref "/doc/project/checklist.md#coverage-model-added" >}}
[TB_LINT_SETUP]:                      {{<relref "/doc/project/checklist.md#tb_lint_setup" >}}
[PRE_VERIFIED_SUB_MODULES_V1]:        {{<relref "/doc/project/checklist.md#pre-verified-sub-modules-v1" >}}
[DESIGN_SPEC_REVIEWED]:               {{<relref "/doc/project/checklist.md#design-spec-reviewed" >}}
[TESTPLAN_REVIEWED]:                  {{<relref "/doc/project/checklist.md#testplan-reviewed" >}}
[STD_TEST_CATEGORIES_PLANNED]:        {{<relref "/doc/project/checklist.md#std-test-categories-planned" >}}
[V2_CHECKLIST_SCOPED]:                {{<relref "/doc/project/checklist.md#v2-checklist-scoped" >}}

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
Integration   | [PRE_VERIFIED_SUB_MODULES_V2][]         | Waived      | prim_arbiter to be verified later
Issues        | [NO_HIGH_PRIORITY_ISSUES_PENDING][]     | Done        |
Issues        | [ALL_LOW_PRIORITY_ISSUES_ROOT_CAUSED][] | Done        |
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
[PRE_VERIFIED_SUB_MODULES_V2]:        {{<relref "/doc/project/checklist.md#pre_verified_sub_modules_v2" >}}
[NO_HIGH_PRIORITY_ISSUES_PENDING]:    {{<relref "/doc/project/checklist.md#no_high_priority_issues_pending" >}}
[ALL_LOW_PRIORITY_ISSUES_ROOT_CAUSED]:{{<relref "/doc/project/checklist.md#all_low_priority_issues_root_caused" >}}
[DV_DOC_TESTPLAN_REVIEWED]:           {{<relref "/doc/project/checklist.md#dv_doc_testplan_reviewed" >}}
[V3_CHECKLIST_SCOPED]:                {{<relref "/doc/project/checklist.md#v3_checklist_scoped" >}}

### V2S

 Type         | Item                                    | Resolution  | Note/Collaterals
--------------|-----------------------------------------|-------------|------------------
Documentation | [SEC_CM_TESTPLAN_COMPLETED][]           | Not Started |
Tests         | [FPV_SEC_CM_VERIFIED][]                 | Not Started |
Tests         | [SIM_SEC_CM_VERIFIED][]                 | Not Started |
Coverage      | [SIM_COVERAGE_REVIEWED][]               | Not Started |
Review        | [SEC_CM_DV_REVIEWED][]                  | Not Started |

[SEC_CM_TESTPLAN_COMPLETED]:          {{<relref "/doc/project/checklist.md#sec_cm_testplan_completed" >}}
[FPV_SEC_CM_VERIFIED]:                {{<relref "/doc/project/checklist.md#fpv_sec_cm_verified" >}}
[SIM_SEC_CM_VERIFIED]:                {{<relref "/doc/project/checklist.md#sim_sec_cm_verified" >}}
[SIM_COVERAGE_REVIEWED]:              {{<relref "/doc/project/checklist.md#sim_coverage_reviewed" >}}
[SEC_CM_DV_REVIEWED]:                 {{<relref "/doc/project/checklist.md#sec_cm_dv_reviewed" >}}

### V3

 Type         | Item                              | Resolution  | Note/Collaterals
--------------|-----------------------------------|-------------|------------------
Documentation | [DESIGN_DELTAS_CAPTURED_V3][]     | N/A         |
Tests         | [X_PROP_ANALYSIS_COMPLETED][]     | Waived      | tool setup in progress
Tests         | [FPV_ASSERTIONS_PROVEN_AT_V3][]   | N/A         |
Regression    | [SIM_NIGHTLY_REGRESSION_AT_100][] | Done        |
Coverage      | [SIM_CODE_COVERAGE_AT_100][]      | Done        | [xbar_cov_excl.el][]
Coverage      | [SIM_FUNCTIONAL_COVERAGE_AT_100][]| Done        |
Coverage      | [FPV_CODE_COVERAGE_AT_100][]      | N/A         |
Coverage      | [FPV_COI_COVERAGE_AT_100][]       | N/A         |
Code Quality  | [ALL_TODOS_RESOLVED][]            | Done        |
Code Quality  | [NO_TOOL_WARNINGS_THROWN][]       | Done        | Waived warning due to using 'force' to connect the signal
Code Quality  | [TB_LINT_COMPLETE][]              | Not Started |
Integration   | [PRE_VERIFIED_SUB_MODULES_V3][]   | Waived      | prim_arbiter to be verified later
Issues        | [NO_ISSUES_PENDING][]             | Done        |
Review        | Reviewer(s)                       | Done        | @eunchan @sriyerg
Review        | Signoff date                      | Done        | 2019-11-07

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

[xbar_cov_excl.el]: https://github.com/weicaiyang/opentitan/blob/6cd55ad23aac96374bfa0bec315b904c6ffbdb8f/hw/ip/tlul/dv/cov/xbar_cov_excl.el
