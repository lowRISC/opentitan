---
title: "AES Checklist"
---

This checklist is for [Hardware Stage]({{< relref "/doc/project/development_stages.md" >}}) transitions for the [AES peripheral.]({{<relref "hw/ip/aes/doc" >}})
All checklist items refer to the content in the [Checklist.]({{< relref "/doc/project/checklist.md" >}})

## Design Checklist

### D1

Type          | Item                  | Resolution  | Note/Collaterals
--------------|-----------------------|-------------|------------------
Documentation | [SPEC_COMPLETE][]     | Done        | [AES Design Spec]({{<relref "hw/ip/aes/doc" >}})
Documentation | [CSR_DEFINED][]       | Done        |
RTL           | [CLKRST_CONNECTED][]  | Done        |
RTL           | [IP_TOP][]            | Done        |
RTL           | [IP_INSTANTIABLE][]   | Done        |
RTL           | [MEM_INSTANCED_80][]  | N/A         |
RTL           | [FUNC_IMPLEMENTED][]  | Done        |
RTL           | [ASSERT_KNOWN_ADDED][]| Done        |
Code Quality  | [LINT_SETUP][]        | Done        |
Review        | Signoff date          | Done        | 2019-11-05

[SPEC_COMPLETE]:      {{<relref "/doc/project/checklist.md#spec-complete" >}}
[CSR_DEFINED]:        {{<relref "/doc/project/checklist.md#csr-defined" >}}
[CLKRST_CONNECTED]:   {{<relref "/doc/project/checklist.md#clkrst-connected" >}}
[IP_TOP]:             {{<relref "/doc/project/checklist.md#ip-top" >}}
[IP_INSTANTIABLE]:    {{<relref "/doc/project/checklist.md#ip-instantiable" >}}
[MEM_INSTANCED_80]:   {{<relref "/doc/project/checklist.md#mem-instanced-80" >}}
[FUNC_IMPLEMENTED]:   {{<relref "/doc/project/checklist.md#func-implemented" >}}
[ASSERT_KNOWN_ADDED]: {{<relref "/doc/project/checklist.md#assert-known-added" >}}
[LINT_SETUP]:         {{<relref "/doc/project/checklist.md#lint-setup" >}}

### D2

Type          | Item                    | Resolution  | Note/Collaterals
--------------|-------------------------|-------------|------------------
Documentation | [NEW_FEATURES][]        | N/A         |
Documentation | [BLOCK_DIAGRAM][]       | N/A         |
Documentation | [DOC_INTERFACE][]       | N/A         |
Documentation | [MISSING_FUNC][]        | Done        |
Documentation | [FEATURE_FROZEN][]      | Done        |
RTL           | [FEATURE_COMPLETE][]    | Done        |
RTL           | [AREA_SANITY_CHECK][]   | Done        |
RTL           | [PORT_FROZEN][]         | Done        |
RTL           | [ARCHITECTURE_FROZEN][] | Done        |
RTL           | [REVIEW_TODO][]         | Done        |
RTL           | [STYLE_X][]             | Done        |
Code Quality  | [LINT_PASS][]           | Done        |
Code Quality  | [CDC_SETUP][]           | N/A         |
Code Quality  | [FPGA_TIMING][]         | Done        |
Code Quality  | [CDC_SYNCMACRO][]       | N/A         |
Review        | Signoff date            | Done        | 2019-11-05

[NEW_FEATURES]:        {{<relref "/doc/project/checklist.md#new-features" >}}
[BLOCK_DIAGRAM]:       {{<relref "/doc/project/checklist.md#block-diagram" >}}
[DOC_INTERFACE]:       {{<relref "/doc/project/checklist.md#doc-interface" >}}
[MISSING_FUNC]:        {{<relref "/doc/project/checklist.md#missing-func" >}}
[FEATURE_FROZEN]:      {{<relref "/doc/project/checklist.md#feature-frozen" >}}
[FEATURE_COMPLETE]:    {{<relref "/doc/project/checklist.md#feature-complete" >}}
[AREA_SANITY_CHECK]:   {{<relref "/doc/project/checklist.md#area-sanity-check" >}}
[PORT_FROZEN]:         {{<relref "/doc/project/checklist.md#port-frozen" >}}
[ARCHITECTURE_FROZEN]: {{<relref "/doc/project/checklist.md#architecture-frozen" >}}
[REVIEW_TODO]:         {{<relref "/doc/project/checklist.md#review-todo" >}}
[STYLE_X]:             {{<relref "/doc/project/checklist.md#style-x" >}}
[LINT_PASS]:           {{<relref "/doc/project/checklist.md#lint-pass" >}}
[CDC_SETUP]:           {{<relref "/doc/project/checklist.md#cdc-setup" >}}
[CDC_SYNCMACRO]:       {{<relref "/doc/project/checklist.md#cdc-syncmacro" >}}
[FPGA_TIMING]:         {{<relref "/doc/project/checklist.md#fpga-timing" >}}

### D3

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
Review        | Signoff date            | Not Started |

[NEW_FEATURES_D3]:      {{<relref "/doc/project/checklist.md#new-features-d3" >}}
[TODO_COMPLETE]:        {{<relref "/doc/project/checklist.md#todo-complete" >}}
[LINT_COMPLETE]:        {{<relref "/doc/project/checklist.md#lint-complete" >}}
[CDC_COMPLETE]:         {{<relref "/doc/project/checklist.md#cdc-complete" >}}
[REVIEW_RTL]:           {{<relref "/doc/project/checklist.md#review-rtl" >}}
[REVIEW_DBG]:           {{<relref "/doc/project/checklist.md#review-dbg" >}}
[REVIEW_DELETED_FF]:    {{<relref "/doc/project/checklist.md#review-deleted-ff" >}}
[REVIEW_SW_CSR]:        {{<relref "/doc/project/checklist.md#review-sw-csr" >}}
[REVIEW_SW_FATAL_ERR]:  {{<relref "/doc/project/checklist.md#review-sw-fatal-err" >}}
[REVIEW_SW_CHANGE]:     {{<relref "/doc/project/checklist.md#review-sw-change" >}}
[REVIEW_SW_ERRATA]:     {{<relref "/doc/project/checklist.md#review-sw-errata" >}}

## Verification Checklist

### V1

 Type         | Item                                  | Resolution  | Note/Collaterals
--------------|---------------------------------------|-------------|------------------
Documentation | [DV_PLAN_DRAFT_COMPLETED][]           | Done        | [AES DV Plan]({{<relref "hw/ip/aes/doc/dv_plan" >}})
Documentation | [TESTPLAN_COMPLETED][]                | Done        | [AES Testplan]({{<relref "hw/ip/aes/doc/dv_plan/index.md#testplan" >}})
Testbench     | [TB_TOP_CREATED][]                    | Done        |
Testbench     | [PRELIMINARY_ASSERTION_CHECKS_ADDED][]| Done        |
Testbench     | [SIM_TB_ENV_CREATED][]                | Done        |
Testbench     | [SIM_RAL_MODEL_GEN_AUTOMATED][]       | Done        |
Testbench     | [CSR_CHECK_GEN_AUTOMATED][]           | Done        |
Testbench     | [TB_GEN_AUTOMATED][]                  | N/A         |
Tests         | [SIM_SANITY_TEST_PASSING][]           | Done        |
Tests         | [SIM_CSR_MEM_TEST_SUITE_PASSING][]    | Done        |
Tests         | [FPV_MAIN_ASSERTIONS_PROVEN][]        | N/A         |
Tool Setup    | [SIM_ALT_TOOL_SETUP][]                | Done        | Xcelium (signoff), VCS (alt)
Regression    | [SIM_SANITY_REGRESSION_SETUP][]       | Done        |
Regression    | [SIM_NIGHTLY_REGRESSION_SETUP][]      | Done        |
Regression    | [FPV_REGRESSION_SETUP][]              | N/A         |
Coverage      | [SIM_COVERAGE_MODEL_ADDED][]          | Done        |
Integration   | [PRE_VERIFIED_SUB_MODULES_V1][]       | N/A         |
Review        | [DESIGN_SPEC_REVIEWED][]              | Done        |
Review        | [DV_PLAN_TESTPLAN_REVIEWED][]         | Done        |
Review        | [STD_TEST_CATEGORIES_PLANNED][]       | Done        | Exception (Power)
Review        | [V2_CHECKLIST_SCOPED][]               | Done        |
Review        | Reviewer(s)                           | Done        | @sriyerg, @weicai, @eunchan
Review        | Signoff date                          | Done        | 2020-03-17

[DV_PLAN_DRAFT_COMPLETED]:            {{<relref "/doc/project/checklist.md#dv-plan-draft-completed" >}}
[TESTPLAN_COMPLETED]:                 {{<relref "/doc/project/checklist.md#testplan-completed" >}}
[TB_TOP_CREATED]:                     {{<relref "/doc/project/checklist.md#tb-top-created" >}}
[PRELIMINARY_ASSERTION_CHECKS_ADDED]: {{<relref "/doc/project/checklist.md#preliminary-assertion-checks-added" >}}
[SIM_TB_ENV_CREATED]:                 {{<relref "/doc/project/checklist.md#sim-tb-env-created" >}}
[SIM_RAL_MODEL_GEN_AUTOMATED]:        {{<relref "/doc/project/checklist.md#sim-ral-model-gen-automated" >}}
[CSR_CHECK_GEN_AUTOMATED]:            {{<relref "/doc/project/checklist.md#csr-check-gen-automated" >}}
[TB_GEN_AUTOMATED]:                   {{<relref "/doc/project/checklist.md#tb-gen-automated" >}}
[SIM_SANITY_TEST_PASSING]:            {{<relref "/doc/project/checklist.md#sim-sanity-test-passing" >}}
[SIM_CSR_MEM_TEST_SUITE_PASSING]:     {{<relref "/doc/project/checklist.md#sim-csr-mem-test-suite-passing" >}}
[FPV_MAIN_ASSERTIONS_PROVEN]:         {{<relref "/doc/project/checklist.md#fpv-main-assertions-proven" >}}
[SIM_ALT_TOOL_SETUP]:                 {{<relref "/doc/project/checklist.md#sim-alt-tool-setup" >}}
[SIM_SANITY_REGRESSION_SETUP]:        {{<relref "/doc/project/checklist.md#sim-sanity-regression-setup" >}}
[SIM_NIGHTLY_REGRESSION_SETUP]:       {{<relref "/doc/project/checklist.md#sim-nightly-regression-setup" >}}
[FPV_REGRESSION_SETUP]:               {{<relref "/doc/project/checklist.md#fpv-regression-setup" >}}
[SIM_COVERAGE_MODEL_ADDED]:           {{<relref "/doc/project/checklist.md#sim-coverage-model-added" >}}
[PRE_VERIFIED_SUB_MODULES_V1]:        {{<relref "/doc/project/checklist.md#pre-verified-sub-modules-v1" >}}
[DESIGN_SPEC_REVIEWED]:               {{<relref "/doc/project/checklist.md#design-spec-reviewed" >}}
[DV_PLAN_TESTPLAN_REVIEWED]:          {{<relref "/doc/project/checklist.md#dv-plan-testplan-reviewed" >}}
[STD_TEST_CATEGORIES_PLANNED]:        {{<relref "/doc/project/checklist.md#std-test-categories-planned" >}}
[V2_CHECKLIST_SCOPED]:                {{<relref "/doc/project/checklist.md#v2-checklist-scoped" >}}

### V2

 Type         | Item                                    | Resolution  | Note/Collaterals
--------------|-----------------------------------------|-------------|------------------
Documentation | [DESIGN_DELTAS_CAPTURED_V2][]           | Not started |
Documentation | [DV_PLAN_COMPLETED][]                   | Not started |
Testbench     | [ALL_INTERFACES_EXERCISED][]            | Not started |
Testbench     | [ALL_ASSERTION_CHECKS_ADDED][]          | Not started |
Testbench     | [SIM_TB_ENV_COMPLETED][]                | Not started |
Tests         | [SIM_ALL_TESTS_PASSING][]               | Not started |
Tests         | [FPV_ALL_ASSERTIONS_WRITTEN][]          | Not started |
Tests         | [FPV_ALL_ASSUMPTIONS_REVIEWED][]        | Not started |
Tests         | [SIM_FW_SIMULATED][]                    | Not started |
Regression    | [SIM_NIGHTLY_REGRESSION_V2][]           | Not started |
Coverage      | [SIM_CODE_COVERAGE_V2][]                | Not started |
Coverage      | [SIM_FUNCTIONAL_COVERAGE_V2][]          | Not started |
Coverage      | [FPV_CODE_COVERAGE_V2][]                | Not started |
Coverage      | [FPV_COI_COVERAGE_V2][]                 | Not started |
Issues        | [NO_HIGH_PRIORITY_ISSUES_PENDING][]     | Not started |
Issues        | [ALL_LOW_PRIORITY_ISSUES_ROOT_CAUSED][] | Not started |
Integration   | [PRE_VERIFIED_SUB_MODULES_V2][]         | Not started |
Review        | [V3_CHECKLIST_SCOPED][]                 | Not started |
Review        | Reviewer(s)                             | Not started |
Review        | Signoff date                            | Not started |

[DESIGN_DELTAS_CAPTURED_V2]:          {{<relref "/doc/project/checklist.md#design-deltas-captured-v2" >}}
[DV_PLAN_COMPLETED]:                  {{<relref "/doc/project/checklist.md#dv-plan-completed" >}}
[ALL_INTERFACES_EXERCISED]:           {{<relref "/doc/project/checklist.md#all-interfaces-exercised" >}}
[ALL_ASSERTION_CHECKS_ADDED]:         {{<relref "/doc/project/checklist.md#all-assertion-checks-added" >}}
[SIM_TB_ENV_COMPLETED]:               {{<relref "/doc/project/checklist.md#sim-tb-env-completed" >}}
[SIM_ALL_TESTS_PASSING]:              {{<relref "/doc/project/checklist.md#sim-all-tests-passing" >}}
[FPV_ALL_ASSERTIONS_WRITTEN]:         {{<relref "/doc/project/checklist.md#fpv-all-assertions-written" >}}
[FPV_ALL_ASSUMPTIONS_REVIEWED]:       {{<relref "/doc/project/checklist.md#fpv-all-assumptions-reviewed" >}}
[SIM_FW_SIMULATED]:                   {{<relref "/doc/project/checklist.md#sim-fw-simulated" >}}
[SIM_NIGHTLY_REGRESSION_V2]:          {{<relref "/doc/project/checklist.md#sim-nightly-regression-v2" >}}
[SIM_CODE_COVERAGE_V2]:               {{<relref "/doc/project/checklist.md#sim-code-coverage-v2" >}}
[SIM_FUNCTIONAL_COVERAGE_V2]:         {{<relref "/doc/project/checklist.md#sim-functional-coverage-v2" >}}
[FPV_CODE_COVERAGE_V2]:               {{<relref "/doc/project/checklist.md#fpv-code-coverage-v2" >}}
[FPV_COI_COVERAGE_V2]:                {{<relref "/doc/project/checklist.md#fpv-coi-coverage-v2" >}}
[NO_HIGH_PRIORITY_ISSUES_PENDING]:    {{<relref "/doc/project/checklist.md#no-high-priority-issues-pending" >}}
[ALL_LOW_PRIORITY_ISSUES_ROOT_CAUSED]:{{<relref "/doc/project/checklist.md#all-low-priority-issues-root-caused" >}}
[PRE_VERIFIED_SUB_MODULES_V2]:        {{<relref "/doc/project/checklist.md#pre-verified-sub-modules-v2" >}}
[V3_CHECKLIST_SCOPED]:                {{<relref "/doc/project/checklist.md#v3-checklist-scoped" >}}

### V3

 Type         | Item                              | Resolution  | Note/Collaterals
--------------|-----------------------------------|-------------|------------------
Documentation | [DESIGN_DELTAS_CAPTURED_V3][]     | Not started |
Testbench     | [ALL_TODOS_RESOLVED][]            | Not started |
Tests         | [X_PROP_ANALYSIS_COMPLETED][]     | Not started |
Tests         | [FPV_ASSERTIONS_PROVEN_AT_V3][]   | Not started |
Regression    | [SIM_NIGHTLY_REGRESSION_AT_V3][]  | Not started |
Coverage      | [SIM_CODE_COVERAGE_AT_100][]      | Not started |
Coverage      | [SIM_FUNCTIONAL_COVERAGE_AT_100][]| Not started |
Coverage      | [FPV_CODE_COVERAGE_AT_100][]      | Not started |
Coverage      | [FPV_COI_COVERAGE_AT_100][]       | Not started |
Issues        | [NO_ISSUES_PENDING][]             | Not started |
Code Quality  | [NO_TOOL_WARNINGS_THROWN][]       | Not started |
Integration   | [PRE_VERIFIED_SUB_MODULES_V3][]   | Not started |
Review        | Reviewer(s)                       | Not started |
Review        | Signoff date                      | Not started |

[DESIGN_DELTAS_CAPTURED_V3]:     {{<relref "/doc/project/checklist.md#design-deltas-captured-v3" >}}
[ALL_TODOS_RESOLVED]:            {{<relref "/doc/project/checklist.md#all-todos-resolved" >}}
[X_PROP_ANALYSIS_COMPLETED]:     {{<relref "/doc/project/checklist.md#x-prop-analysis-completed" >}}
[FPV_ASSERTIONS_PROVEN_AT_V3]:   {{<relref "/doc/project/checklist.md#fpv-assertions-proven-at-v3" >}}
[SIM_NIGHTLY_REGRESSION_AT_V3]:  {{<relref "/doc/project/checklist.md#sim-nightly-regression-at-v3" >}}
[SIM_CODE_COVERAGE_AT_100]:      {{<relref "/doc/project/checklist.md#sim-code-coverage-at-100" >}}
[SIM_FUNCTIONAL_COVERAGE_AT_100]:{{<relref "/doc/project/checklist.md#sim-functional-coverage-at-100" >}}
[FPV_CODE_COVERAGE_AT_100]:      {{<relref "/doc/project/checklist.md#fpv-code-coverage-at-100" >}}
[FPV_COI_COVERAGE_AT_100]:       {{<relref "/doc/project/checklist.md#fpv-coi-coverage-at-100" >}}
[NO_ISSUES_PENDING]:             {{<relref "/doc/project/checklist.md#no-issues-pending" >}}
[NO_TOOL_WARNINGS_THROWN]:       {{<relref "/doc/project/checklist.md#no-tool-warnings-thrown" >}}
[PRE_VERIFIED_SUB_MODULES_V3]:   {{<relref "/doc/project/checklist.md#pre-verified-sub-modules-v3" >}}
