---
title: "Padctrl Checklist"
---

This checklist is for [Hardware Stage]({{< relref "/doc/project/development_stages.md" >}}) transitions for the [Padctrl peripheral.]({{< relref "./" >}})
All checklist items refer to the content in the [Checklist.]({{< relref "/doc/project/checklist.md" >}})

## Design Checklist

### D1

Type          | Item                  | Resolution  | Note/Collaterals
--------------|-----------------------|-------------|------------------
Documentation | [SPEC_COMPLETE][]     | Done        | [Padctrl spec]({{< relref "./" >}})
Documentation | [CSR_DEFINED][]       | Done        |
RTL           | [CLKRST_CONNECTED][]  | Done        |
RTL           | [IP_TOP][]            | Done        |
RTL           | [IP_INSTANCED][]      | Done        |
RTL           | [MEM_INSTANCED_80][]  | Done        |
RTL           | [FUNC_IMPLEMENTED][]  | Done        |
RTL           | [ASSERT_KNOWN_ADDED][]| Done        |
Code Quality  | [LINT_SETUP][]        | Done        |
Review        | Reviewer(s)           | Done        | @sjgitty @weicai
Review        | Signoff date          | Done        | 2019-11-8


[SPEC_COMPLETE]:      {{<relref "/doc/project/checklist.md#spec-complete" >}}
[CSR_DEFINED]:        {{<relref "/doc/project/checklist.md#csr-defined" >}}
[CLKRST_CONNECTED]:   {{<relref "/doc/project/checklist.md#clkrst-connected" >}}
[IP_TOP]:             {{<relref "/doc/project/checklist.md#ip-top" >}}
[IP_INSTANCED]:       {{<relref "/doc/project/checklist.md#ip-instanced" >}}
[MEM_INSTANCED_80]:   {{<relref "/doc/project/checklist.md#mem-instanced-80" >}}
[FUNC_IMPLEMENTED]:   {{<relref "/doc/project/checklist.md#func-implemented" >}}
[ASSERT_KNOWN_ADDED]: {{<relref "/doc/project/checklist.md#assert-known-added" >}}
[LINT_SETUP]:         {{<relref "/doc/project/checklist.md#lint-setup" >}}

### D2

Type          | Item                    | Resolution  | Note/Collaterals
--------------|-------------------------|-------------|------------------
Documentation | [NEW_FEATURES][]        | Not Started |
Documentation | [BLOCK_DIAGRAM][]       | Done        |
Documentation | [DOC_INTERFACE][]       | Done        |
Documentation | [MISSING_FUNC][]        | Not Started |
Documentation | [FEATURE_FROZEN][]      | Not Started |
RTL           | [FEATURE_COMPLETE][]    | Not Started |
RTL           | [AREA_SANITY_CHECK][]   | Not Started |
RTL           | [PORT_FROZEN][]         | Not Started |
RTL           | [ARCHITECTURE_FROZEN][] | Not Started |
RTL           | [REVIEW_TODO][]         | Not Started |
RTL           | [STYLE_X][]             | Not Started |
Code Quality  | [LINT_PASS][]           | Done        |
Code Quality  | [CDC_SETUP][]           | Done        |
Code Quality  | [FPGA_TIMING][]         | Not Started |
Code Quality  | [CDC_SYNCMACRO][]       | Done        |
Review        | Reviewer(s)             | Not Started |
Review        | Signoff date            | Not Started |

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
Review        | Reviewer(s)             | Not Started |
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
Documentation | [DV_PLAN_DRAFT_COMPLETED][]           | In Progress |
Documentation | [TESTPLAN_COMPLETED][]                | In Progress |
Testbench     | [TB_TOP_CREATED][]                    | Done        |
Testbench     | [PRELIMINARY_ASSERTION_CHECKS_ADDED][]| Done        |
Testbench     | [TB_ENV_CREATED][]                    | Done        |
Testbench     | [RAL_MODEL_GEN_AUTOMATED][]           | N/A         | This block uses FPV
Tests         | [SANITY_TEST_PASSING][]               | Done        |
Tests         | [CSR_MEM_TEST_SUITE_PASSING][]        | In Progress | FPV CSR tests being developed by @cindychip
Tool Setup    | [ALT_TOOL_SETUP][]                    | N/A         |
Regression    | [SANITY_REGRESSION_SETUP][]           | Done        |
Regression    | [NIGHTLY_REGRESSION_SETUP][]          | Not Started |
Coverage      | [COVERAGE_MODEL_ADDED][]              | Not Started |
Integration   | [PRE_VERIFIED_SUB_MODULES_V1][]       | N/A         |
Review        | [DESIGN_SPEC_REVIEWED][]              | Not Started |
Review        | [DV_PLAN_TESTPLAN_REVIEWED][]         | Not Started |
Review        | [STD_TEST_CATEGORIES_PLANNED][]       | Not Started |
Review        | [V2_CHECKLIST_SCOPED][]               | Not Started |
Review        | Reviewer(s)                           | Not Started |
Review        | Signoff date                          | Not Started |


[DV_PLAN_DRAFT_COMPLETED]:            {{<relref "/doc/project/checklist.md#dv-plan-draft-completed" >}}
[TESTPLAN_COMPLETED]:                 {{<relref "/doc/project/checklist.md#testplan-completed" >}}
[TB_TOP_CREATED]:                     {{<relref "/doc/project/checklist.md#tb-top-created" >}}
[PRELIMINARY_ASSERTION_CHECKS_ADDED]: {{<relref "/doc/project/checklist.md#preliminary-assertion-checks-added" >}}
[TB_ENV_CREATED]:                     {{<relref "/doc/project/checklist.md#tb-env-created" >}}
[RAL_MODEL_GEN_AUTOMATED]:            {{<relref "/doc/project/checklist.md#ral-model-gen-automated" >}}
[SANITY_TEST_PASSING]:                {{<relref "/doc/project/checklist.md#sanity-test-passing" >}}
[CSR_MEM_TEST_SUITE_PASSING]:         {{<relref "/doc/project/checklist.md#csr-mem-test-suite-passing" >}}
[ALT_TOOL_SETUP]:                     {{<relref "/doc/project/checklist.md#alt-tool-setup" >}}
[SANITY_REGRESSION_SETUP]:            {{<relref "/doc/project/checklist.md#sanity-regression-setup" >}}
[NIGHTLY_REGRESSION_SETUP]:           {{<relref "/doc/project/checklist.md#nightly-regression-setup" >}}
[COVERAGE_MODEL_ADDED]:               {{<relref "/doc/project/checklist.md#coverage-model-added" >}}
[PRE_VERIFIED_SUB_MODULES_V1]:        {{<relref "/doc/project/checklist.md#pre-verified-sub-modules-v1" >}}
[DESIGN_SPEC_REVIEWED]:               {{<relref "/doc/project/checklist.md#design-spec-reviewed" >}}
[DV_PLAN_TESTPLAN_REVIEWED]:          {{<relref "/doc/project/checklist.md#dv-plan-testplan-reviewed" >}}
[STD_TEST_CATEGORIES_PLANNED]:        {{<relref "/doc/project/checklist.md#std-test-categories-planned" >}}
[V2_CHECKLIST_SCOPED]:                {{<relref "/doc/project/checklist.md#v2-checklist-scoped" >}}

### V2

 Type         | Item                                    | Resolution  | Note/Collaterals
--------------|-----------------------------------------|-------------|------------------
Documentation | [DESIGN_DELTAS_CAPTURED_V2][]           | Not Started |
Documentation | [DV_PLAN_COMPLETED][]                   | Not Started |
Testbench     | [ALL_INTERFACES_EXERCISED][]            | Not Started |
Testbench     | [ALL_ASSERTION_CHECKS_ADDED][]          | Not Started |
Testbench     | [TB_ENV_COMPLETED][]                    | Not Started |
Tests         | [ALL_TESTS_PASSING][]                   | Not Started |
Tests         | [FW_SIMULATED][]                        | Not Started |
Regression    | [NIGHTLY_REGRESSION_V2][]               | Not Started |
Coverage      | [CODE_COVERAGE_V2][]                    | Not Started |
Coverage      | [FUNCTIONAL_COVERAGE_V2][]              | Not Started |
Issues        | [NO_HIGH_PRIORITY_ISSUES_PENDING][]     | Not Started |
Issues        | [ALL_LOW_PRIORITY_ISSUES_ROOT_CAUSED][] | Not Started |
Integration   | [PRE_VERIFIED_SUB_MODULES_V2][]         | Not Started |
Review        | [V3_CHECKLIST_SCOPED][]                 | Not Started |
Review        | Reviewer(s)                             | Not Started |
Review        | Signoff date                            | Not Started |


[DESIGN_DELTAS_CAPTURED_V2]:          {{<relref "/doc/project/checklist.md#design-deltas-captured-v2" >}}
[DV_PLAN_COMPLETED]:                  {{<relref "/doc/project/checklist.md#dv-plan-completed">}}
[ALL_INTERFACES_EXERCISED]:           {{<relref "/doc/project/checklist.md#all-interfaces-exercised" >}}
[ALL_ASSERTION_CHECKS_ADDED]:         {{<relref "/doc/project/checklist.md#all-assertion-checks-added" >}}
[TB_ENV_COMPLETED]:                   {{<relref "/doc/project/checklist.md#tb-env-completed">}}
[ALL_TESTS_PASSING]:                  {{<relref "/doc/project/checklist.md#all-tests-passing">}}
[FW_SIMULATED]:                       {{<relref "/doc/project/checklist.md#fw-simulated" >}}
[NIGHTLY_REGRESSION_V2]:              {{<relref "/doc/project/checklist.md#nightly-regression-v2" >}}
[CODE_COVERAGE_V2]:                   {{<relref "/doc/project/checklist.md#code-coverage-v2">}}
[FUNCTIONAL_COVERAGE_V2]:             {{<relref "/doc/project/checklist.md#functional-coverage-v2" >}}
[NO_HIGH_PRIORITY_ISSUES_PENDING]:    {{<relref "/doc/project/checklist.md#no-high-priority-issues-pending" >}}
[ALL_LOW_PRIORITY_ISSUES_ROOT_CAUSED]:{{<relref "/doc/project/checklist.md#all-low-priority-issues-root-caused" >}}
[PRE_VERIFIED_SUB_MODULES_V2]:        {{<relref "/doc/project/checklist.md#pre-verified-sub-modules-v2" >}}
[V3_CHECKLIST_SCOPED]:                {{<relref "/doc/project/checklist.md#v3-checklist-scoped" >}}

### V3

 Type         | Item                              | Resolution  | Note/Collaterals
--------------|-----------------------------------|-------------|------------------
Documentation | [DESIGN_DELTAS_CAPTURED_V3][]     | Not Started |
Testbench     | [ALL_TODOS_RESOLVED][]            | Not Started |
Tests         | [X_PROP_ANALYSIS_COMPLETED][]     | Not Started |
Regression    | [NIGHTLY_REGRESSION_AT_100][]     | Not Started |
Coverage      | [CODE_COVERAGE_AT_100][]          | Not Started |
Coverage      | [FUNCTIONAL_COVERAGE_AT_100][]    | Not Started |
Issues        | [NO_ISSUES_PENDING][]             | Not Started |
Code Quality  | [NO_TOOL_WARNINGS_THROWN][]       | Not Started |
Integration   | [PRE_VERIFIED_SUB_MODULES_V3][]   | Not Started |
Review        | Reviewer(s)                       | Not Started |
Review        | Signoff date                      | Not Started |

[DESIGN_DELTAS_CAPTURED_V3]:    {{<relref "/doc/project/checklist.md#design-deltas-captured-v3" >}}
[ALL_TODOS_RESOLVED]:           {{<relref "/doc/project/checklist.md#all-todos-resolved" >}}
[X_PROP_ANALYSIS_COMPLETED]:    {{<relref "/doc/project/checklist.md#x-prop-analysis-completed" >}}
[NIGHTLY_REGRESSION_AT_100]:    {{<relref "/doc/project/checklist.md#nightly-regression-at-100" >}}
[CODE_COVERAGE_AT_100]:         {{<relref "/doc/project/checklist.md#code-coverage-at-100" >}}
[FUNCTIONAL_COVERAGE_AT_100]:   {{<relref "/doc/project/checklist.md#functional-coverage-at-100" >}}
[NO_ISSUES_PENDING]:            {{<relref "/doc/project/checklist.md#no-issues-pending" >}}
[NO_TOOL_WARNINGS_THROWN]:      {{<relref "/doc/project/checklist.md#no-tool-warnings-thrown" >}}
[PRE_VERIFIED_SUB_MODULES_V3]:  {{<relref "/doc/project/checklist.md#pre-verified-sub-modules-v3" >}}
