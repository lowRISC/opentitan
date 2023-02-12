# TL-UL Checklist

This checklist is for [Hardware Stage](../../../../../doc/project_governance/development_stages.md) transitions for the [TL-UL component.](../../../../ip/tlul/README.md)
All checklist items refer to the content in the [Checklist](../../../../../doc/project_governance/checklist/README.md).

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

[TL-UL Spec]:         ../../../../ip/tlul/README.md
[crossbar_tool]:      ../../../../../util/tlgen/README.md

[SPEC_COMPLETE]:              ../../../../../doc/project_governance/checklist/README.md#spec_complete
[CSR_DEFINED]:                ../../../../../doc/project_governance/checklist/README.md#csr_defined
[CLKRST_CONNECTED]:           ../../../../../doc/project_governance/checklist/README.md#clkrst_connected
[IP_TOP]:                     ../../../../../doc/project_governance/checklist/README.md#ip_top
[IP_INSTANTIABLE]:            ../../../../../doc/project_governance/checklist/README.md#ip_instantiable
[PHYSICAL_MACROS_DEFINED_80]: ../../../../../doc/project_governance/checklist/README.md#physical_macros_defined_80
[FUNC_IMPLEMENTED]:           ../../../../../doc/project_governance/checklist/README.md#func_implemented
[ASSERT_KNOWN_ADDED]:         ../../../../../doc/project_governance/checklist/README.md#assert_known_added
[LINT_SETUP]:                 ../../../../../doc/project_governance/checklist/README.md#lint_setup

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
RTL           | [PORT_FROZEN][]           | Done        | Targeting for current top_earlgrey( Port can be changed later based on top_earlgrey config)
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

[NEW_FEATURES]:          ../../../../../doc/project_governance/checklist/README.md#new_features
[BLOCK_DIAGRAM]:         ../../../../../doc/project_governance/checklist/README.md#block_diagram
[DOC_INTERFACE]:         ../../../../../doc/project_governance/checklist/README.md#doc_interface
[DOC_INTEGRATION_GUIDE]: ../../../../../doc/project_governance/checklist/README.md#doc_integration_guide
[MISSING_FUNC]:          ../../../../../doc/project_governance/checklist/README.md#missing_func
[FEATURE_FROZEN]:        ../../../../../doc/project_governance/checklist/README.md#feature_frozen
[FEATURE_COMPLETE]:      ../../../../../doc/project_governance/checklist/README.md#feature_complete
[PORT_FROZEN]:           ../../../../../doc/project_governance/checklist/README.md#port_frozen
[ARCHITECTURE_FROZEN]:   ../../../../../doc/project_governance/checklist/README.md#architecture_frozen
[REVIEW_TODO]:           ../../../../../doc/project_governance/checklist/README.md#review_todo
[STYLE_X]:               ../../../../../doc/project_governance/checklist/README.md#style_x
[CDC_SYNCMACRO]:         ../../../../../doc/project_governance/checklist/README.md#cdc_syncmacro
[LINT_PASS]:             ../../../../../doc/project_governance/checklist/README.md#lint_pass
[CDC_SETUP]:             ../../../../../doc/project_governance/checklist/README.md#cdc_setup
[RDC_SETUP]:             ../../../../../doc/project_governance/checklist/README.md#rdc_setup
[AREA_CHECK]:            ../../../../../doc/project_governance/checklist/README.md#area_check
[TIMING_CHECK]:          ../../../../../doc/project_governance/checklist/README.md#timing_check
[SEC_CM_DOCUMENTED]:     ../../../../../doc/project_governance/checklist/README.md#sec_cm_documented

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

[SEC_CM_ASSETS_LISTED]:    ../../../../../doc/project_governance/checklist/README.md#sec_cm_assets_listed
[SEC_CM_IMPLEMENTED]:      ../../../../../doc/project_governance/checklist/README.md#sec_cm_implemented
[SEC_CM_RND_CNST]:         ../../../../../doc/project_governance/checklist/README.md#sec_cm_rnd_cnst
[SEC_CM_NON_RESET_FLOPS]:  ../../../../../doc/project_governance/checklist/README.md#sec_cm_non_reset_flops
[SEC_CM_SHADOW_REGS]:      ../../../../../doc/project_governance/checklist/README.md#sec_cm_shadow_regs
[SEC_CM_RTL_REVIEWED]:     ../../../../../doc/project_governance/checklist/README.md#sec_cm_rtl_reviewed
[SEC_CM_COUNCIL_REVIEWED]: ../../../../../doc/project_governance/checklist/README.md#sec_cm_council_reviewed

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

[NEW_FEATURES_D3]:      ../../../../../doc/project_governance/checklist/README.md#new_features_d3
[TODO_COMPLETE]:        ../../../../../doc/project_governance/checklist/README.md#todo_complete
[LINT_COMPLETE]:        ../../../../../doc/project_governance/checklist/README.md#lint_complete
[CDC_COMPLETE]:         ../../../../../doc/project_governance/checklist/README.md#cdc_complete
[RDC_COMPLETE]:         ../../../../../doc/project_governance/checklist/README.md#rdc_complete
[REVIEW_RTL]:           ../../../../../doc/project_governance/checklist/README.md#review_rtl
[REVIEW_DELETED_FF]:    ../../../../../doc/project_governance/checklist/README.md#review_deleted_ff
[REVIEW_SW_CHANGE]:     ../../../../../doc/project_governance/checklist/README.md#review_sw_change
[REVIEW_SW_ERRATA]:     ../../../../../doc/project_governance/checklist/README.md#review_sw_errata

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

[XBAR DV document]:                   ../../../../ip/tlul/doc/dv/README.md
[XBAR Testplan]:                      ../../../../ip/tlul/doc/dv/README.md#testplan

[DV_DOC_DRAFT_COMPLETED]:             ../../../../../doc/project_governance/checklist/README.md#dv-doc-draft-completed
[TESTPLAN_COMPLETED]:                 ../../../../../doc/project_governance/checklist/README.md#testplan-completed
[TB_TOP_CREATED]:                     ../../../../../doc/project_governance/checklist/README.md#tb-top-created
[PRELIMINARY_ASSERTION_CHECKS_ADDED]: ../../../../../doc/project_governance/checklist/README.md#preliminary-assertion-checks-added
[TB_ENV_CREATED]:                     ../../../../../doc/project_governance/checklist/README.md#tb-env-created
[RAL_MODEL_GEN_AUTOMATED]:            ../../../../../doc/project_governance/checklist/README.md#ral-model-gen-automated
[TB_GEN_AUTOMATED]:                   ../../../../../doc/project_governance/checklist/README.md#tb-gen-automated
[SMOKE_TEST_PASSING]:                 ../../../../../doc/project_governance/checklist/README.md#smoke-test-passing
[CSR_MEM_TEST_SUITE_PASSING]:         ../../../../../doc/project_governance/checklist/README.md#csr-mem-test-suite-passing
[ALT_TOOL_SETUP]:                     ../../../../../doc/project_governance/checklist/README.md#alt-tool-setup
[SMOKE_REGRESSION_SETUP]:             ../../../../../doc/project_governance/checklist/README.md#smoke-regression-setup
[NIGHTLY_REGRESSION_SETUP]:           ../../../../../doc/project_governance/checklist/README.md#nightly-regression-setup
[COVERAGE_MODEL_ADDED]:               ../../../../../doc/project_governance/checklist/README.md#coverage-model-added
[TB_LINT_SETUP]:                      ../../../../../doc/project_governance/checklist/README.md#tb_lint_setup
[PRE_VERIFIED_SUB_MODULES_V1]:        ../../../../../doc/project_governance/checklist/README.md#pre-verified-sub-modules-v1
[DESIGN_SPEC_REVIEWED]:               ../../../../../doc/project_governance/checklist/README.md#design-spec-reviewed
[TESTPLAN_REVIEWED]:                  ../../../../../doc/project_governance/checklist/README.md#testplan-reviewed
[STD_TEST_CATEGORIES_PLANNED]:        ../../../../../doc/project_governance/checklist/README.md#std-test-categories-planned
[V2_CHECKLIST_SCOPED]:                ../../../../../doc/project_governance/checklist/README.md#v2-checklist-scoped

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

[DESIGN_DELTAS_CAPTURED_V2]:          ../../../../../doc/project_governance/checklist/README.md#design_deltas_captured_v2
[DV_DOC_COMPLETED]:                   ../../../../../doc/project_governance/checklist/README.md#dv_doc_completed
[FUNCTIONAL_COVERAGE_IMPLEMENTED]:    ../../../../../doc/project_governance/checklist/README.md#functional_coverage_implemented
[ALL_INTERFACES_EXERCISED]:           ../../../../../doc/project_governance/checklist/README.md#all_interfaces_exercised
[ALL_ASSERTION_CHECKS_ADDED]:         ../../../../../doc/project_governance/checklist/README.md#all_assertion_checks_added
[SIM_TB_ENV_COMPLETED]:               ../../../../../doc/project_governance/checklist/README.md#sim_tb_env_completed
[SIM_ALL_TESTS_PASSING]:              ../../../../../doc/project_governance/checklist/README.md#sim_all_tests_passing
[FPV_ALL_ASSERTIONS_WRITTEN]:         ../../../../../doc/project_governance/checklist/README.md#fpv_all_assertions_written
[FPV_ALL_ASSUMPTIONS_REVIEWED]:       ../../../../../doc/project_governance/checklist/README.md#fpv_all_assumptions_reviewed
[SIM_FW_SIMULATED]:                   ../../../../../doc/project_governance/checklist/README.md#sim_fw_simulated
[SIM_NIGHTLY_REGRESSION_V2]:          ../../../../../doc/project_governance/checklist/README.md#sim_nightly_regression_v2
[SIM_CODE_COVERAGE_V2]:               ../../../../../doc/project_governance/checklist/README.md#sim_code_coverage_v2
[SIM_FUNCTIONAL_COVERAGE_V2]:         ../../../../../doc/project_governance/checklist/README.md#sim_functional_coverage_v2
[FPV_CODE_COVERAGE_V2]:               ../../../../../doc/project_governance/checklist/README.md#fpv_code_coverage_v2
[FPV_COI_COVERAGE_V2]:                ../../../../../doc/project_governance/checklist/README.md#fpv_coi_coverage_v2
[PRE_VERIFIED_SUB_MODULES_V2]:        ../../../../../doc/project_governance/checklist/README.md#pre_verified_sub_modules_v2
[NO_HIGH_PRIORITY_ISSUES_PENDING]:    ../../../../../doc/project_governance/checklist/README.md#no_high_priority_issues_pending
[ALL_LOW_PRIORITY_ISSUES_ROOT_CAUSED]:../../../../../doc/project_governance/checklist/README.md#all_low_priority_issues_root_caused
[DV_DOC_TESTPLAN_REVIEWED]:           ../../../../../doc/project_governance/checklist/README.md#dv_doc_testplan_reviewed
[V3_CHECKLIST_SCOPED]:                ../../../../../doc/project_governance/checklist/README.md#v3_checklist_scoped

### V2S

 Type         | Item                                    | Resolution  | Note/Collaterals
--------------|-----------------------------------------|-------------|------------------
Documentation | [SEC_CM_TESTPLAN_COMPLETED][]           | Not Started |
Tests         | [FPV_SEC_CM_VERIFIED][]                 | Not Started |
Tests         | [SIM_SEC_CM_VERIFIED][]                 | Not Started |
Coverage      | [SIM_COVERAGE_REVIEWED][]               | Not Started |
Review        | [SEC_CM_DV_REVIEWED][]                  | Not Started |

[SEC_CM_TESTPLAN_COMPLETED]:          ../../../../../doc/project_governance/checklist/README.md#sec_cm_testplan_completed
[FPV_SEC_CM_VERIFIED]:                ../../../../../doc/project_governance/checklist/README.md#fpv_sec_cm_verified
[SIM_SEC_CM_VERIFIED]:                ../../../../../doc/project_governance/checklist/README.md#sim_sec_cm_verified
[SIM_COVERAGE_REVIEWED]:              ../../../../../doc/project_governance/checklist/README.md#sim_coverage_reviewed
[SEC_CM_DV_REVIEWED]:                 ../../../../../doc/project_governance/checklist/README.md#sec_cm_dv_reviewed

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

[DESIGN_DELTAS_CAPTURED_V3]:     ../../../../../doc/project_governance/checklist/README.md#design_deltas_captured_v3
[X_PROP_ANALYSIS_COMPLETED]:     ../../../../../doc/project_governance/checklist/README.md#x_prop_analysis_completed
[FPV_ASSERTIONS_PROVEN_AT_V3]:   ../../../../../doc/project_governance/checklist/README.md#fpv_assertions_proven_at_v3
[SIM_NIGHTLY_REGRESSION_AT_V3]:  ../../../../../doc/project_governance/checklist/README.md#sim_nightly_regression_at_v3
[SIM_CODE_COVERAGE_AT_100]:      ../../../../../doc/project_governance/checklist/README.md#sim_code_coverage_at_100
[SIM_FUNCTIONAL_COVERAGE_AT_100]:../../../../../doc/project_governance/checklist/README.md#sim_functional_coverage_at_100
[FPV_CODE_COVERAGE_AT_100]:      ../../../../../doc/project_governance/checklist/README.md#fpv_code_coverage_at_100
[FPV_COI_COVERAGE_AT_100]:       ../../../../../doc/project_governance/checklist/README.md#fpv_coi_coverage_at_100
[ALL_TODOS_RESOLVED]:            ../../../../../doc/project_governance/checklist/README.md#all_todos_resolved
[NO_TOOL_WARNINGS_THROWN]:       ../../../../../doc/project_governance/checklist/README.md#no_tool_warnings_thrown
[TB_LINT_COMPLETE]:              ../../../../../doc/project_governance/checklist/README.md#tb_lint_complete
[PRE_VERIFIED_SUB_MODULES_V3]:   ../../../../../doc/project_governance/checklist/README.md#pre_verified_sub_modules_v3
[NO_ISSUES_PENDING]:             ../../../../../doc/project_governance/checklist/README.md#no_issues_pending

[xbar_cov_excl.el]: https://github.com/weicaiyang/opentitan/blob/6cd55ad23aac96374bfa0bec315b904c6ffbdb8f/hw/ip/tlul/dv/cov/xbar_cov_excl.el
