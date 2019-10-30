{{% lowrisc-doc-hdr GPIO Checklist }}

This checklist is for [Hardware Stage](../../../../doc/ug/hw_stages.md)
transitions for the [GPIO peripheral.](gpio.md) All checklist
items refer to the content in the [Checklist.](../../../../doc/rm/checklist.md)

## Design Checklist

### D1

Type          | Item                  | Resolution  | Note/Collaterals
--------------|-----------------------|-------------|------------------
Documentation | [SPEC_COMPLETE][]     | Done        | [GPIO Spec][]
Documentation | [CSR_DEFINED][]       | Done        | [GPIO CSR][]
RTL           | [CLKRST_CONNECTED][]  | Done        |
RTL           | [IP_TOP][]            | Done        |
RTL           | [IP_INSTANCED][]      | Done        |
RTL           | [MEM_INSTANCED_80][]  | N/A         |
RTL           | [FUNC_IMPLEMENTED][]  | Done        |
RTL           | [ASSERT_KNOWN_ADDED][]| Done        |
Code Quality  | [LINT_SETUP][]        | Done        |
              |                       |             |
Review        | [D1_REVIEWED][]       | Not Started |
Review        | Reviewer(s)           | Not Started |
Review        | Signoff date          | Not Started | 2019-10-30

[GPIO Spec]: gpio.md
[GPIO CSR]: ../data/gpio.hjson


[SPEC_COMPLETE]:      ../../../../doc/rm/checklist.md#spec_complete
[CSR_DEFINED]:        ../../../../doc/rm/checklist.md#csr_defined
[CLKRST_CONNECTED]:   ../../../../doc/rm/checklist.md#clkrst_connected
[IP_TOP]:             ../../../../doc/rm/checklist.md#ip_top
[IP_INSTANCED]:       ../../../../doc/rm/checklist.md#ip_instanced
[MEM_INSTANCED_80]:   ../../../../doc/rm/checklist.md#mem_instanced_80
[FUNC_IMPLEMENTED]:   ../../../../doc/rm/checklist.md#func_implemented
[ASSERT_KNOWN_ADDED]: ../../../../doc/rm/checklist.md#assert_known_added
[LINT_SETUP]:         ../../../../doc/rm/checklist.md#lint_setup
[D1_REVIEWED]:        ../../../../doc/rm/checklist.md#d1_reviewed

### D2

Type          | Item                    | Resolution  | Note/Collaterals
--------------|-------------------------|-------------|------------------
Documentation | [NEW_FEATURES][]        | N/A         | 
Documentation | [BLOCK_DIAGRAM][]       | N/A         |
Documentation | [DOC_INTERFACE][]       | Done        |
Documentation | [MISSING_FUNC][]        | N/A         |
Documentation | [FEATURE_FROZEN][]      | Done        |
RTL           | [FEATURE_COMPLETE][]    | Done        |
RTL           | [AREA_SANITY_CHECK][]   | Done        |
RTL           | [PORT_FROZEN][]         | Done        |
RTL           | [ARCHITECTURE_FROZEN][] | Done        |
RTL           | [REVIEW_TODO][]         | Done        |
RTL           | [STYLE_X][]             | N/A         | No assignment of X
Code Quality  | [LINT_PASS][]           | Done        | Lint waivers reviewed
Code Quality  | [CDC_SETUP][]           | N/A         | No CDC path
Code Quality  | [FPGA_TIMING][]         | Done        | Fmax 50MHz on NexysVideo
Code Quality  | [CDC_SYNCMACRO][]       | N/A         |
              |                         |             |
Review        | [D2_REVIEWED][]         | Not Started |
Review        | Reviewer(s)             | Not Started |
Review        | Signoff date            | Not Started | 2019-10-30

[NEW_FEATURES]:        ../../../../doc/rm/checklist.md#new_features
[BLOCK_DIAGRAM]:       ../../../../doc/rm/checklist.md#block_diagram
[DOC_INTERFACE]:       ../../../../doc/rm/checklist.md#doc_interface
[MISSING_FUNC]:        ../../../../doc/rm/checklist.md#missing_func
[FEATURE_FROZEN]:      ../../../../doc/rm/checklist.md#feature_frozen
[FEATURE_COMPLETE]:    ../../../../doc/rm/checklist.md#feature_complete
[AREA_SANITY_CHECK]:   ../../../../doc/rm/checklist.md#area_sanity_check
[DEBUG_BUS]:           ../../../../doc/rm/checklist.md#debug_bus
[PORT_FROZEN]:         ../../../../doc/rm/checklist.md#port_frozen
[ARCHITECTURE_FROZEN]: ../../../../doc/rm/checklist.md#architecture_frozen
[REVIEW_TODO]:         ../../../../doc/rm/checklist.md#review_todo
[STYLE_X]:             ../../../../doc/rm/checklist.md#style_x
[STYLE_LINT_SETUP]:    ../../../../doc/rm/checklist.md#style_lint_setup
[LINT_PASS]:           ../../../../doc/rm/checklist.md#lint_pass
[CDC_SETUP]:           ../../../../doc/rm/checklist.md#cdc_setup
[CDC_SYNCMACRO]:       ../../../../doc/rm/checklist.md#cdc_syncmacro
[FPGA_TIMING]:         ../../../../doc/rm/checklist.md#fpga_timing
[D2_REVIEWED]:         ../../../../doc/rm/checklist.md#d2_reviewed

### D3

 Type         | Item                    | Resolution  | Note/Collaterals
--------------|-------------------------|-------------|------------------
Documentation | [NEW_FEATURES_D3][]     | N/A         |
RTL           | [TODO_COMPLETE][]       | Done        | No TODO
Code Quality  | [LINT_COMPLETE][]       | Done        |
Code Quality  | [CDC_COMPLETE][]        | N/A         |
Review        | [REVIEW_RTL][]          | Not Started |
Review        | [REVIEW_DELETED_FF][]   | N/A         | Not reported by FPGA tool
Review        | [REVIEW_SW_CSR][]       | Not Started |
Review        | [REVIEW_SW_FATAL_ERR][] | Not Started |
Review        | [REVIEW_SW_CHANGE][]    | Not Started |
Review        | [REVIEW_SW_ERRATA][]    | Not Started |
              |                         |             |
Review        | [D3_REVIEWED][]         | Not Started |
Review        | Reviewer(s)             | Not Started |
Review        | Signoff date            | Not Started | 2019-10-30

[NEW_FEATURES_D3]:      ../../../../doc/rm/checklist.md#new_features_d3
[TODO_COMPLETE]:        ../../../../doc/rm/checklist.md#todo_complete
[LINT_COMPLETE]:        ../../../../doc/rm/checklist.md#lint_complete
[CDC_COMPLETE]:         ../../../../doc/rm/checklist.md#cdc_complete
[REVIEW_RTL]:           ../../../../doc/rm/checklist.md#review_rtl
[REVIEW_DBG]:           ../../../../doc/rm/checklist.md#review_dbg
[REVIEW_DELETED_FF]:    ../../../../doc/rm/checklist.md#review_deleted_ff
[REVIEW_SW_CSR]:        ../../../../doc/rm/checklist.md#review_sw_csr
[REVIEW_SW_FATAL_ERR]:  ../../../../doc/rm/checklist.md#review_sw_fatal_err
[REVIEW_SW_CHANGE]:     ../../../../doc/rm/checklist.md#review_sw_change
[REVIEW_SW_ERRATA]:     ../../../../doc/rm/checklist.md#review_sw_errata
[D3_REVIEWED]:          ../../../../doc/rm/checklist.md#d3_reviewed

## Verification Checklist

### Checklists for milestone V1

 Type         | Item                                  | Resolution      | Note/Collaterals
--------------|---------------------------------------|-----------------|------------------
Documentation | [DV_PLAN_DRAFT_COMPLETED][]           | Done            |
Documentation | [TESTPLAN_COMPLETED][]                | Done            |
Testbench     | [TB_TOP_CREATED][]                    | Done            |
Testbench     | [PRELIMINARY_ASSERTION_CHECKS_ADDED][]| Done            |
Testbench     | [TB_ENV_CREATED][]                    | Done            |
Testbench     | [RAL_MODEL_GEN_AUTOMATED][]           | Done            |
Testbench     | [TB_GEN_AUTOMATED][]                  | N/A             |
Tests         | [SANITY_TEST_PASSING][]               | Done            |
Tests         | [CSR_MEM_TEST_SUITE_PASSING][]        | Done            |
Tool Setup    | [ALT_TOOL_SETUP][]                    | Done            |
Regression    | [SANITY_REGRESSION_SETUP][]           | Done w/ waivers | Exception (implemented in local)
Regression    | [NIGHTLY_REGRESSION_SETUP][]          | Done w/ waivers | Exception (implemented in local)
Coverage      | [COVERAGE_MODEL_ADDED][]              | Done            |
Integration   | [PRE_VERIFIED_SUB_MODULES_V1][]       | N/A             |
Review        | [DESIGN_SPEC_REVIEWED][]              | Done            |
Review        | [DV_PLAN_TESTPLAN_REVIEWED][]         | Done            |
Review        | [STD_TEST_CATEGORIES_PLANNED][]       | Done            | Exception (Security, Power, Debug)
Review        | [V2_CHECKLIST_SCOPED][]               | Done            |
Review        | Reviewer(s)                           | Not Started     |
Review        | Signoff date                          | Not Started     |


[DV_PLAN_DRAFT_COMPLETED]:            ../../../../doc/rm/checklist.md#dv_plan_draft_completed
[TESTPLAN_COMPLETED]:                 ../../../../doc/rm/checklist.md#testplan_completed
[TB_TOP_CREATED]:                     ../../../../doc/rm/checklist.md#tb_top_created
[PRELIMINARY_ASSERTION_CHECKS_ADDED]: ../../../../doc/rm/checklist.md#preliminary_assertion_checks_added
[TB_ENV_CREATED]:                     ../../../../doc/rm/checklist.md#tb_env_created
[RAL_MODEL_GEN_AUTOMATED]:            ../../../../doc/rm/checklist.md#ral_model_gen_automated
[TB_GEN_AUTOMATED]:                   ../../../../doc/rm/checklist.md#tb_gen_automated
[SANITY_TEST_PASSING]:                ../../../../doc/rm/checklist.md#sanity_test_passing
[CSR_MEM_TEST_SUITE_PASSING]:         ../../../../doc/rm/checklist.md#csr_mem_test_suite_passing
[ALT_TOOL_SETUP]:                     ../../../../doc/rm/checklist.md#alt_tool_setup
[SANITY_REGRESSION_SETUP]:            ../../../../doc/rm/checklist.md#sanity_regression_setup
[NIGHTLY_REGRESSION_SETUP]:           ../../../../doc/rm/checklist.md#nightly_regression_setup
[COVERAGE_MODEL_ADDED]:               ../../../../doc/rm/checklist.md#coverage_model_added
[PRE_VERIFIED_SUB_MODULES_V1]:        ../../../../doc/rm/checklist.md#pre_verified_sub_modules_v1
[DESIGN_SPEC_REVIEWED]:               ../../../../doc/rm/checklist.md#design_spec_reviewed
[DV_PLAN_TESTPLAN_REVIEWED]:          ../../../../doc/rm/checklist.md#dv_plan_testplan_reviewed
[STD_TEST_CATEGORIES_PLANNED]:        ../../../../doc/rm/checklist.md#std_test_categories_planned
[V2_CHECKLIST_SCOPED]:                ../../../../doc/rm/checklist.md#v2_checklist_scoped

### Checklists for milestone V2

 Type         | Item                                    | Resolution  | Note/Collaterals
--------------|-----------------------------------------|-------------|------------------
Documentation | [DESIGN_DELTAS_CAPTURED][]              | N/A         |
Documentation | [DV_PLAN_COMPLETED][]                   | Done        |
Testbench     | [ALL_INTERFACES_EXERCISED][]            | Done        |
Testbench     | [ALL_ASSERTION_CHECKS_ADDED][]          | Done        |
Testbench     | [TB_ENV_COMPLETED][]                    | Done        |
Tests         | [ALL_TESTS_PASSING][]                   | In Progress |
Tests         | [FW_SIMULATED][]                        | N/A         |
Regression    | [NIGHTLY_REGRESSION_V2][]               | Done        |
Coverage      | [CODE_COVERAGE_V2][]                    | Done        |
Coverage      | [FUNCTIONAL_COVERAGE_V2][]              | Done        |
Issues        | [NO_HIGH_PRIORITY_ISSUES_PENDING][]     | Done        |
Issues        | [ALL_LOW_PRIORITY_ISSUES_ROOT_CAUSED][] | In Progress | [#41][], [#45][]
Integration   | [PRE_VERIFIED_SUB_MODULES_V2][]         | N/A         |
Review        | [V3_CHECKLIST_SCOPED][]                 | Done        |
Review        | Reviewer(s)                             | Not Started |
Review        | Signoff date                            | Not Started |

[#41]: https://github.com/lowRISC/opentitan/issues/41
[#45]: https://github.com/lowRISC/opentitan/issues/45

[DESIGN_DELTAS_CAPTURED]:             ../../../../doc/rm/checklist.md#design_deltas_captured
[DV_PLAN_COMPLETED]:                  ../../../../doc/rm/checklist.md#dv_plan_completed
[ALL_INTERFACES_EXERCISED]:           ../../../../doc/rm/checklist.md#all_interfaces_exercised
[ALL_ASSERTION_CHECKS_ADDED]:         ../../../../doc/rm/checklist.md#all_assertion_checks_added
[TB_ENV_COMPLETED]:                   ../../../../doc/rm/checklist.md#tb_env_completed
[ALL_TESTS_PASSING]:                  ../../../../doc/rm/checklist.md#all_tests_passing
[FW_SIMULATED]:                       ../../../../doc/rm/checklist.md#fw_simulated
[NIGHTLY_REGRESSION_V2]:              ../../../../doc/rm/checklist.md#nightly_regression_v2
[CODE_COVERAGE_V2]:                   ../../../../doc/rm/checklist.md#code_coverage_v2
[FUNCTIONAL_COVERAGE_V2]:             ../../../../doc/rm/checklist.md#functional_coverage_v2
[NO_HIGH_PRIORITY_ISSUES_PENDING]:    ../../../../doc/rm/checklist.md#no_high_priority_issues_pending
[ALL_LOW_PRIORITY_ISSUES_ROOT_CAUSED]:../../../../doc/rm/checklist.md#all_low_priority_issues_root_caused
[PRE_VERIFIED_SUB_MODULES_V2]:        ../../../../doc/rm/checklist.md#pre_verified_sub_modules_v2
[V3_CHECKLIST_SCOPED]:                ../../../../doc/rm/checklist.md#v3_checklist_scoped

### Checklists for milestone V3

 Type         | Item                              | Resolution  | Note/Collaterals
--------------|-----------------------------------|-------------|------------------
Documentation | [DESIGN_DELTAS_CAPTURED_IF_ANY][] | Done        |
Testbench     | [ALL_TODOS_RESOLVED][]            | Done        |
Tests         | [X_PROP_ANALYSIS_COMPLETED][]     | Waived      | Revisit later. Tool setup in progress.
Regression    | [NIGHTLY_REGRESSION_AT_100][]     | In Progress |
Coverage      | [CODE_COVERAGE_AT_100][]          | In Progress |
Coverage      | [FUNCTIONAL_COVERAGE_AT_100][]    | In Progress |
Issues        | [NO_ISSUES_PENDING][]             | Done        |
Code Quality  | [NO_TOOL_WARNINGS_THROWN][]       | Done        |
Integration   | [PRE_VERIFIED_SUB_MODULES_V3][]   | N/A         |
Review        | Reviewer(s)                       | Not Started |
Review        | Signoff date                      | Not Started |

[DESIGN_DELTAS_CAPTURED_IF_ANY]:../../../../doc/rm/checklist.md#design_deltas_captured_if_any
[ALL_TODOS_RESOLVED]:           ../../../../doc/rm/checklist.md#all_todos_resolved
[X_PROP_ANALYSIS_COMPLETED]:    ../../../../doc/rm/checklist.md#x_prop_analysis_completed
[NIGHTLY_REGRESSION_AT_100]:    ../../../../doc/rm/checklist.md#nightly_regression_at_100
[CODE_COVERAGE_AT_100]:         ../../../../doc/rm/checklist.md#code_coverage_at_100
[FUNCTIONAL_COVERAGE_AT_100]:   ../../../../doc/rm/checklist.md#functional_coverage_at_100
[NO_ISSUES_PENDING]:            ../../../../doc/rm/checklist.md#no_issues_pending
[NO_TOOL_WARNINGS_THROWN]:      ../../../../doc/rm/checklist.md#no_tool_warnings_thrown
[PRE_VERIFIED_SUB_MODULES_V3]:  ../../../../doc/rm/checklist.md#pre_verified_sub_modules_v3
