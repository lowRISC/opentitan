---
title: "${name.upper()} Checklist"
---

<!--
NOTE: This is a template checklist document that is required to be copied over to the 'doc'
directory for a new design that transitions from L0 (Specification) to L1 (Development)
stage, and updated as needed. Once done, please remove this comment before checking it in.
-->
This checklist is for [Hardware Stage](/doc/project_governance/development_stages.md) transitions for the [${name.upper()} peripheral.](../README.md)
All checklist items refer to the content in the [Checklist.](/doc/project_governance/checklist/README.md)

<%text>## Design Checklist</%text>

<%text>### D1</%text>

Type          | Item                           | Resolution  | Note/Collaterals
--------------|--------------------------------|-------------|------------------
Documentation | [SPEC_COMPLETE][]              | Not Started | [${name.upper()} Design Spec](../README.md)
Documentation | [CSR_DEFINED][]                | Not Started |
RTL           | [CLKRST_CONNECTED][]           | Not Started |
RTL           | [IP_TOP][]                     | Not Started |
RTL           | [IP_INSTANTIABLE][]            | Not Started |
RTL           | [PHYSICAL_MACROS_DEFINED_80][] | Not Started |
RTL           | [FUNC_IMPLEMENTED][]           | Not Started |
RTL           | [ASSERT_KNOWN_ADDED][]         | Not Started |
Code Quality  | [LINT_SETUP][]                 | Not Started |
Security      | [SEC_CM_SCOPED][]              | Not Started |

[SPEC_COMPLETE]:              /doc/project_governance/checklist/README.md#spec_complete
[CSR_DEFINED]:                /doc/project_governance/checklist/README.md#csr_defined
[CLKRST_CONNECTED]:           /doc/project_governance/checklist/README.md#clkrst_connected
[IP_TOP]:                     /doc/project_governance/checklist/README.md#ip_top
[IP_INSTANTIABLE]:            /doc/project_governance/checklist/README.md#ip_instantiable
[PHYSICAL_MACROS_DEFINED_80]: /doc/project_governance/checklist/README.md#physical_macros_defined_80
[FUNC_IMPLEMENTED]:           /doc/project_governance/checklist/README.md#func_implemented
[ASSERT_KNOWN_ADDED]:         /doc/project_governance/checklist/README.md#assert_known_added
[LINT_SETUP]:                 /doc/project_governance/checklist/README.md#lint_setup
[SEC_CM_SCOPED]:              /doc/project_governance/checklist/README.md#sec_cm_scoped

<%text>### D2</%text>

Type          | Item                      | Resolution  | Note/Collaterals
--------------|---------------------------|-------------|------------------
Documentation | [NEW_FEATURES][]          | Not Started |
Documentation | [BLOCK_DIAGRAM][]         | Not Started |
Documentation | [DOC_INTERFACE][]         | Not Started |
Documentation | [DOC_INTEGRATION_GUIDE][] | Not Started |
Documentation | [MISSING_FUNC][]          | Not Started |
Documentation | [FEATURE_FROZEN][]        | Not Started |
RTL           | [FEATURE_COMPLETE][]      | Not Started |
RTL           | [PORT_FROZEN][]           | Not Started |
RTL           | [ARCHITECTURE_FROZEN][]   | Not Started |
RTL           | [REVIEW_TODO][]           | Not Started |
RTL           | [STYLE_X][]               | Not Started |
RTL           | [CDC_SYNCMACRO][]         | Not Started |
Code Quality  | [LINT_PASS][]             | Not Started |
Code Quality  | [CDC_SETUP][]             | Not Started |
Code Quality  | [RDC_SETUP][]             | Not Started |
Code Quality  | [AREA_CHECK][]            | Not Started |
Code Quality  | [TIMING_CHECK][]          | Not Started |
Security      | [SEC_CM_DOCUMENTED][]     | Not Started |

[NEW_FEATURES]:          /doc/project_governance/checklist/README.md#new_features
[BLOCK_DIAGRAM]:         /doc/project_governance/checklist/README.md#block_diagram
[DOC_INTERFACE]:         /doc/project_governance/checklist/README.md#doc_interface
[DOC_INTEGRATION_GUIDE]: /doc/project_governance/checklist/README.md#doc_integration_guide
[MISSING_FUNC]:          /doc/project_governance/checklist/README.md#missing_func
[FEATURE_FROZEN]:        /doc/project_governance/checklist/README.md#feature_frozen
[FEATURE_COMPLETE]:      /doc/project_governance/checklist/README.md#feature_complete
[PORT_FROZEN]:           /doc/project_governance/checklist/README.md#port_frozen
[ARCHITECTURE_FROZEN]:   /doc/project_governance/checklist/README.md#architecture_frozen
[REVIEW_TODO]:           /doc/project_governance/checklist/README.md#review_todo
[STYLE_X]:               /doc/project_governance/checklist/README.md#style_x
[CDC_SYNCMACRO]:         /doc/project_governance/checklist/README.md#cdc_syncmacro
[LINT_PASS]:             /doc/project_governance/checklist/README.md#lint_pass
[CDC_SETUP]:             /doc/project_governance/checklist/README.md#cdc_setup
[RDC_SETUP]:             /doc/project_governance/checklist/README.md#rdc_setup
[AREA_CHECK]:            /doc/project_governance/checklist/README.md#area_check
[TIMING_CHECK]:          /doc/project_governance/checklist/README.md#timing_check
[SEC_CM_DOCUMENTED]:     /doc/project_governance/checklist/README.md#sec_cm_documented

<%text>### D2S</%text>

 Type         | Item                         | Resolution  | Note/Collaterals
--------------|------------------------------|-------------|------------------
Security      | [SEC_CM_ASSETS_LISTED][]     | Not Started |
Security      | [SEC_CM_IMPLEMENTED][]       | Not Started |
Security      | [SEC_CM_RND_CNST][]          | Not Started |
Security      | [SEC_CM_NON_RESET_FLOPS][]   | Not Started |
Security      | [SEC_CM_SHADOW_REGS][]       | Not Started |
Security      | [SEC_CM_RTL_REVIEWED][]      | Not Started |
Security      | [SEC_CM_COUNCIL_REVIEWED][]  | Not Started |

[SEC_CM_ASSETS_LISTED]:    /doc/project_governance/checklist/README.md#sec_cm_assets_listed
[SEC_CM_IMPLEMENTED]:      /doc/project_governance/checklist/README.md#sec_cm_implemented
[SEC_CM_RND_CNST]:         /doc/project_governance/checklist/README.md#sec_cm_rnd_cnst
[SEC_CM_NON_RESET_FLOPS]:  /doc/project_governance/checklist/README.md#sec_cm_non_reset_flops
[SEC_CM_SHADOW_REGS]:      /doc/project_governance/checklist/README.md#sec_cm_shadow_regs
[SEC_CM_RTL_REVIEWED]:     /doc/project_governance/checklist/README.md#sec_cm_rtl_reviewed
[SEC_CM_COUNCIL_REVIEWED]: /doc/project_governance/checklist/README.md#sec_cm_council_reviewed

<%text>### D3</%text>

 Type         | Item                    | Resolution  | Note/Collaterals
--------------|-------------------------|-------------|------------------
Documentation | [NEW_FEATURES_D3][]     | Not Started |
RTL           | [TODO_COMPLETE][]       | Not Started |
Code Quality  | [LINT_COMPLETE][]       | Not Started |
Code Quality  | [CDC_COMPLETE][]        | Not Started |
Code Quality  | [RDC_COMPLETE][]        | Not Started |
Review        | [REVIEW_RTL][]          | Not Started |
Review        | [REVIEW_DELETED_FF][]   | Not Started |
Review        | [REVIEW_SW_CHANGE][]    | Not Started |
Review        | [REVIEW_SW_ERRATA][]    | Not Started |
Review        | Reviewer(s)             | Not Started |
Review        | Signoff date            | Not Started |

[NEW_FEATURES_D3]:      /doc/project_governance/checklist/README.md#new_features_d3
[TODO_COMPLETE]:        /doc/project_governance/checklist/README.md#todo_complete
[LINT_COMPLETE]:        /doc/project_governance/checklist/README.md#lint_complete
[CDC_COMPLETE]:         /doc/project_governance/checklist/README.md#cdc_complete
[RDC_COMPLETE]:         /doc/project_governance/checklist/README.md#rdc_complete
[REVIEW_RTL]:           /doc/project_governance/checklist/README.md#review_rtl
[REVIEW_DELETED_FF]:    /doc/project_governance/checklist/README.md#review_deleted_ff
[REVIEW_SW_CHANGE]:     /doc/project_governance/checklist/README.md#review_sw_change
[REVIEW_SW_ERRATA]:     /doc/project_governance/checklist/README.md#review_sw_errata

<%text>## Verification Checklist</%text>

<%text>### V1</%text>

 Type         | Item                                  | Resolution  | Note/Collaterals
--------------|---------------------------------------|-------------|------------------
Documentation | [DV_DOC_DRAFT_COMPLETED][]            | Not Started | [${name.upper()} DV document](../dv/README.md)
Documentation | [TESTPLAN_COMPLETED][]                | Not Started | [${name.upper()} Testplan](../dv/README.md#testplan)
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

[DV_DOC_DRAFT_COMPLETED]:             /doc/project_governance/checklist/README.md#dv_doc_draft_completed
[TESTPLAN_COMPLETED]:                 /doc/project_governance/checklist/README.md#testplan_completed
[TB_TOP_CREATED]:                     /doc/project_governance/checklist/README.md#tb_top_created
[PRELIMINARY_ASSERTION_CHECKS_ADDED]: /doc/project_governance/checklist/README.md#preliminary_assertion_checks_added
[SIM_TB_ENV_CREATED]:                 /doc/project_governance/checklist/README.md#sim_tb_env_created
[SIM_RAL_MODEL_GEN_AUTOMATED]:        /doc/project_governance/checklist/README.md#sim_ral_model_gen_automated
[CSR_CHECK_GEN_AUTOMATED]:            /doc/project_governance/checklist/README.md#csr_check_gen_automated
[TB_GEN_AUTOMATED]:                   /doc/project_governance/checklist/README.md#tb_gen_automated
[SIM_SMOKE_TEST_PASSING]:             /doc/project_governance/checklist/README.md#sim_smoke_test_passing
[SIM_CSR_MEM_TEST_SUITE_PASSING]:     /doc/project_governance/checklist/README.md#sim_csr_mem_test_suite_passing
[FPV_MAIN_ASSERTIONS_PROVEN]:         /doc/project_governance/checklist/README.md#fpv_main_assertions_proven
[SIM_ALT_TOOL_SETUP]:                 /doc/project_governance/checklist/README.md#sim_alt_tool_setup
[SIM_SMOKE_REGRESSION_SETUP]:         /doc/project_governance/checklist/README.md#sim_smoke_regression_setup
[SIM_NIGHTLY_REGRESSION_SETUP]:       /doc/project_governance/checklist/README.md#sim_nightly_regression_setup
[FPV_REGRESSION_SETUP]:               /doc/project_governance/checklist/README.md#fpv_regression_setup
[SIM_COVERAGE_MODEL_ADDED]:           /doc/project_governance/checklist/README.md#sim_coverage_model_added
[TB_LINT_SETUP]:                      /doc/project_governance/checklist/README.md#tb_lint_setup
[PRE_VERIFIED_SUB_MODULES_V1]:        /doc/project_governance/checklist/README.md#pre_verified_sub_modules_v1
[DESIGN_SPEC_REVIEWED]:               /doc/project_governance/checklist/README.md#design_spec_reviewed
[TESTPLAN_REVIEWED]:                  /doc/project_governance/checklist/README.md#testplan_reviewed
[STD_TEST_CATEGORIES_PLANNED]:        /doc/project_governance/checklist/README.md#std_test_categories_planned
[V2_CHECKLIST_SCOPED]:                /doc/project_governance/checklist/README.md#v2_checklist_scoped

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
Integration   | [PRE_VERIFIED_SUB_MODULES_V2][]         | Not Started |
Issues        | [NO_HIGH_PRIORITY_ISSUES_PENDING][]     | Not Started |
Issues        | [ALL_LOW_PRIORITY_ISSUES_ROOT_CAUSED][] | Not Started |
Review        | [DV_DOC_TESTPLAN_REVIEWED][]            | Not Started |
Review        | [V3_CHECKLIST_SCOPED][]                 | Not Started |

[DESIGN_DELTAS_CAPTURED_V2]:          /doc/project_governance/checklist/README.md#design_deltas_captured_v2
[DV_DOC_COMPLETED]:                   /doc/project_governance/checklist/README.md#dv_doc_completed
[FUNCTIONAL_COVERAGE_IMPLEMENTED]:    /doc/project_governance/checklist/README.md#functional_coverage_implemented
[ALL_INTERFACES_EXERCISED]:           /doc/project_governance/checklist/README.md#all_interfaces_exercised
[ALL_ASSERTION_CHECKS_ADDED]:         /doc/project_governance/checklist/README.md#all_assertion_checks_added
[SIM_TB_ENV_COMPLETED]:               /doc/project_governance/checklist/README.md#sim_tb_env_completed
[SIM_ALL_TESTS_PASSING]:              /doc/project_governance/checklist/README.md#sim_all_tests_passing
[FPV_ALL_ASSERTIONS_WRITTEN]:         /doc/project_governance/checklist/README.md#fpv_all_assertions_written
[FPV_ALL_ASSUMPTIONS_REVIEWED]:       /doc/project_governance/checklist/README.md#fpv_all_assumptions_reviewed
[SIM_FW_SIMULATED]:                   /doc/project_governance/checklist/README.md#sim_fw_simulated
[SIM_NIGHTLY_REGRESSION_V2]:          /doc/project_governance/checklist/README.md#sim_nightly_regression_v2
[SIM_CODE_COVERAGE_V2]:               /doc/project_governance/checklist/README.md#sim_code_coverage_v2
[SIM_FUNCTIONAL_COVERAGE_V2]:         /doc/project_governance/checklist/README.md#sim_functional_coverage_v2
[FPV_CODE_COVERAGE_V2]:               /doc/project_governance/checklist/README.md#fpv_code_coverage_v2
[FPV_COI_COVERAGE_V2]:                /doc/project_governance/checklist/README.md#fpv_coi_coverage_v2
[PRE_VERIFIED_SUB_MODULES_V2]:        /doc/project_governance/checklist/README.md#pre_verified_sub_modules_v2
[NO_HIGH_PRIORITY_ISSUES_PENDING]:    /doc/project_governance/checklist/README.md#no_high_priority_issues_pending
[ALL_LOW_PRIORITY_ISSUES_ROOT_CAUSED]:/doc/project_governance/checklist/README.md#all_low_priority_issues_root_caused
[DV_DOC_TESTPLAN_REVIEWED]:           /doc/project_governance/checklist/README.md#dv_doc_testplan_reviewed
[V3_CHECKLIST_SCOPED]:                /doc/project_governance/checklist/README.md#v3_checklist_scoped

<%text>### V2S</%text>

 Type         | Item                                    | Resolution  | Note/Collaterals
--------------|-----------------------------------------|-------------|------------------
Documentation | [SEC_CM_TESTPLAN_COMPLETED][]           | Not Started |
Tests         | [FPV_SEC_CM_VERIFIED][]                 | Not Started |
Tests         | [SIM_SEC_CM_VERIFIED][]                 | Not Started |
Coverage      | [SIM_COVERAGE_REVIEWED][]               | Not Started |
Review        | [SEC_CM_DV_REVIEWED][]                  | Not Started |

[SEC_CM_TESTPLAN_COMPLETED]:          /doc/project_governance/checklist/README.md#sec_cm_testplan_completed
[FPV_SEC_CM_VERIFIED]:                /doc/project_governance/checklist/README.md#fpv_sec_cm_verified
[SIM_SEC_CM_VERIFIED]:                /doc/project_governance/checklist/README.md#sim_sec_cm_verified
[SIM_COVERAGE_REVIEWED]:              /doc/project_governance/checklist/README.md#sim_coverage_reviewed
[SEC_CM_DV_REVIEWED]:                 /doc/project_governance/checklist/README.md#sec_cm_dv_reviewed

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

[DESIGN_DELTAS_CAPTURED_V3]:     /doc/project_governance/checklist/README.md#design_deltas_captured_v3
[X_PROP_ANALYSIS_COMPLETED]:     /doc/project_governance/checklist/README.md#x_prop_analysis_completed
[FPV_ASSERTIONS_PROVEN_AT_V3]:   /doc/project_governance/checklist/README.md#fpv_assertions_proven_at_v3
[SIM_NIGHTLY_REGRESSION_AT_V3]:  /doc/project_governance/checklist/README.md#sim_nightly_regression_at_v3
[SIM_CODE_COVERAGE_AT_100]:      /doc/project_governance/checklist/README.md#sim_code_coverage_at_100
[SIM_FUNCTIONAL_COVERAGE_AT_100]:/doc/project_governance/checklist/README.md#sim_functional_coverage_at_100
[FPV_CODE_COVERAGE_AT_100]:      /doc/project_governance/checklist/README.md#fpv_code_coverage_at_100
[FPV_COI_COVERAGE_AT_100]:       /doc/project_governance/checklist/README.md#fpv_coi_coverage_at_100
[ALL_TODOS_RESOLVED]:            /doc/project_governance/checklist/README.md#all_todos_resolved
[NO_TOOL_WARNINGS_THROWN]:       /doc/project_governance/checklist/README.md#no_tool_warnings_thrown
[TB_LINT_COMPLETE]:              /doc/project_governance/checklist/README.md#tb_lint_complete
[PRE_VERIFIED_SUB_MODULES_V3]:   /doc/project_governance/checklist/README.md#pre_verified_sub_modules_v3
[NO_ISSUES_PENDING]:             /doc/project_governance/checklist/README.md#no_issues_pending
