---
title: "${name.upper()} Checklist"
---

This checklist is for [Hardware Stage]({{< relref "/doc/ug/hw_stages.md" >}}) transitions for the [${name.upper()} peripheral.]({{< relref "index.md" >}})
All checklist items refer to the content in the [Checklist.]({{< relref "/doc/rm/checklist.md" >}})

## Design Checklist

### D1

Type          | Item                  | Resolution  | Note/Collaterals
--------------|-----------------------|-------------|------------------
Documentation | [SPEC_COMPLETE][]     | Not Started |
Documentation | [CSR_DEFINED][]       | Not Started |
RTL           | [CLKRST_CONNECTED][]  | Not Started |
RTL           | [IP_TOP][]            | Not Started |
RTL           | [IP_INSTANCED][]      | Not Started |
RTL           | [MEM_INSTANCED_80][]  | Not Started |
RTL           | [FUNC_IMPLEMENTED][]  | Not Started |
RTL           | [ASSERT_KNOWN_ADDED][]| Not Started |
Code Quality  | [LINT_SETUP][]        | Not Started |
              |                       |             |
Review        | [D1_REVIEWED][]       | Not Started |
Review        | Reviewer(s)           | Not Started |
Review        | Signoff date          | Not Started |


[SPEC_COMPLETE]:      {{<relref "/doc/rm/checklist.md#spec-complete" >}}
[CSR_DEFINED]:        {{<relref "/doc/rm/checklist.md#csr-defined" >}}
[CLKRST_CONNECTED]:   {{<relref "/doc/rm/checklist.md#clkrst-connected" >}}
[IP_TOP]:             {{<relref "/doc/rm/checklist.md#ip-top" >}}
[IP_INSTANCED]:       {{<relref "/doc/rm/checklist.md#ip-instanced" >}}
[MEM_INSTANCED_80]:   {{<relref "/doc/rm/checklist.md#mem-instanced-80" >}}
[FUNC_IMPLEMENTED]:   {{<relref "/doc/rm/checklist.md#func-implemented" >}}
[ASSERT_KNOWN_ADDED]: {{<relref "/doc/rm/checklist.md#assert-known-added" >}}
[LINT_SETUP]:         {{<relref "/doc/rm/checklist.md#lint-setup" >}}
[D1_REVIEWED]:        {{<relref "/doc/rm/checklist.md#d1-reviewed" >}}

### D2

Type          | Item                    | Resolution  | Note/Collaterals
--------------|-------------------------|-------------|------------------
Documentation | [NEW_FEATURES][]        | Not Started | 
Documentation | [BLOCK_DIAGRAM][]       | Not Started |
Documentation | [DOC_INTERFACE][]       | Not Started |
Documentation | [MISSING_FUNC][]        | Not Started |
Documentation | [FEATURE_FROZEN][]      | Not Started |
RTL           | [FEATURE_COMPLETE][]    | Not Started |
RTL           | [AREA_SANITY_CHECK][]   | Not Started |
RTL           | [PORT_FROZEN][]         | Not Started |
RTL           | [ARCHITECTURE_FROZEN][] | Not Started |
RTL           | [REVIEW_TODO][]         | Not Started |
RTL           | [STYLE_X][]             | Not Started |
Code Quality  | [LINT_PASS][]           | Not Started |
Code Quality  | [CDC_SETUP][]           | Not Started |
Code Quality  | [FPGA_TIMING][]         | Not Started |
Code Quality  | [CDC_SYNCMACRO][]       | Not Started |
              |                         |             |
Review        | [D2_REVIEWED][]         | Not Started |
Review        | Reviewer(s)             | Not Started |
Review        | Signoff date            | Not Started |

[NEW_FEATURES]:        {{<relref "/doc/rm/checklist.md#new-features" >}}
[BLOCK_DIAGRAM]:       {{<relref "/doc/rm/checklist.md#block-diagram" >}}
[DOC_INTERFACE]:       {{<relref "/doc/rm/checklist.md#doc-interface" >}}
[MISSING_FUNC]:        {{<relref "/doc/rm/checklist.md#missing-func" >}}
[FEATURE_FROZEN]:      {{<relref "/doc/rm/checklist.md#feature-frozen" >}}
[FEATURE_COMPLETE]:    {{<relref "/doc/rm/checklist.md#feature-complete" >}}
[AREA_SANITY_CHECK]:   {{<relref "/doc/rm/checklist.md#area-sanity-check" >}}
[DEBUG_BUS]:           {{<relref "/doc/rm/checklist.md#debug-bus" >}}
[PORT_FROZEN]:         {{<relref "/doc/rm/checklist.md#port-frozen" >}}
[ARCHITECTURE_FROZEN]: {{<relref "/doc/rm/checklist.md#architecture-frozen" >}}
[REVIEW_TODO]:         {{<relref "/doc/rm/checklist.md#review-todo" >}}
[STYLE_X]:             {{<relref "/doc/rm/checklist.md#style-x" >}}
[STYLE_LINT_SETUP]:    {{<relref "/doc/rm/checklist.md#style-lint-setup" >}}
[LINT_PASS]:           {{<relref "/doc/rm/checklist.md#lint-pass" >}}
[CDC_SETUP]:           {{<relref "/doc/rm/checklist.md#cdc-setup" >}}
[CDC_SYNCMACRO]:       {{<relref "/doc/rm/checklist.md#cdc-syncmacro" >}}
[FPGA_TIMING]:         {{<relref "/doc/rm/checklist.md#fpga-timing" >}}
[D2_REVIEWED]:         {{<relref "/doc/rm/checklist.md#d2-reviewed" >}}

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
              |                         |             |
Review        | [D3_REVIEWED][]         | Not Started |
Review        | Reviewer(s)             | Not Started |
Review        | Signoff date            | Not Started |

[NEW_FEATURES_D3]:      {{<relref "/doc/rm/checklist.md#new-features-d3" >}}
[TODO_COMPLETE]:        {{<relref "/doc/rm/checklist.md#todo-complete" >}}
[LINT_COMPLETE]:        {{<relref "/doc/rm/checklist.md#lint-complete" >}}
[CDC_COMPLETE]:         {{<relref "/doc/rm/checklist.md#cdc-complete" >}}
[REVIEW_RTL]:           {{<relref "/doc/rm/checklist.md#review-rtl" >}}
[REVIEW_DBG]:           {{<relref "/doc/rm/checklist.md#review-dbg" >}}
[REVIEW_DELETED_FF]:    {{<relref "/doc/rm/checklist.md#review-deleted-ff" >}}
[REVIEW_SW_CSR]:        {{<relref "/doc/rm/checklist.md#review-sw-csr" >}}
[REVIEW_SW_FATAL_ERR]:  {{<relref "/doc/rm/checklist.md#review-sw-fatal-err" >}}
[REVIEW_SW_CHANGE]:     {{<relref "/doc/rm/checklist.md#review-sw-change" >}}
[REVIEW_SW_ERRATA]:     {{<relref "/doc/rm/checklist.md#review-sw-errata" >}}
[D3_REVIEWED]:          {{<relref "/doc/rm/checklist.md#d3-reviewed" >}}

## Verification Checklist

### Checklists for milestone V1

 Type         | Item                                  | Resolution  | Note/Collaterals
--------------|---------------------------------------|-------------|------------------
Documentation | [DV_PLAN_DRAFT_COMPLETED][]           | Not Started | 
Documentation | [TESTPLAN_COMPLETED][]                | Not Started |
Testbench     | [TB_TOP_CREATED][]                    | Not Started |
Testbench     | [PRELIMINARY_ASSERTION_CHECKS_ADDED][]| Not Started |
Testbench     | [TB_ENV_CREATED][]                    | Not Started |
Testbench     | [RAL_MODEL_GEN_AUTOMATED][]           | Not Started |
Testbench     | [TB_GEN_AUTOMATED][]                  | Not Started |
Tests         | [SANITY_TEST_PASSING][]               | Not Started |
Tests         | [CSR_MEM_TEST_SUITE_PASSING][]        | Not Started |
Tool Setup    | [ALT_TOOL_SETUP][]                    | Not Started |
Regression    | [SANITY_REGRESSION_SETUP][]           | Not Started |
Regression    | [NIGHTLY_REGRESSION_SETUP][]          | Not Started |
Coverage      | [COVERAGE_MODEL_ADDED][]              | Not Started |
Integration   | [PRE_VERIFIED_SUB_MODULES_V1][]       | Not Started |
Review        | [DESIGN_SPEC_REVIEWED][]              | Not Started |
Review        | [DV_PLAN_TESTPLAN_REVIEWED][]         | Not Started |
Review        | [STD_TEST_CATEGORIES_PLANNED][]       | Not Started |
Review        | [V2_CHECKLIST_SCOPED][]               | Not Started |
Review        | Reviewer(s)                           | Not Started |
Review        | Signoff date                          | Not Started |


[DV_PLAN_DRAFT_COMPLETED]:            {{<relref "/doc/rm/checklist.md#dv-plan-draft-completed" >}}
[TESTPLAN_COMPLETED]:                 {{<relref "/doc/rm/checklist.md#testplan-completed" >}}
[TB_TOP_CREATED]:                     {{<relref "/doc/rm/checklist.md#tb-top-created" >}}
[PRELIMINARY_ASSERTION_CHECKS_ADDED]: {{<relref "/doc/rm/checklist.md#preliminary-assertion-checks-added" >}}
[TB_ENV_CREATED]:                     {{<relref "/doc/rm/checklist.md#tb-env-created" >}}
[RAL_MODEL_GEN_AUTOMATED]:            {{<relref "/doc/rm/checklist.md#ral-model-gen-automated" >}}
[TB_GEN_AUTOMATED]:                   {{<relref "/doc/rm/checklist.md#tb-gen-automated"
>}}
[SANITY_TEST_PASSING]:                {{<relref "/doc/rm/checklist.md#sanity-test-passing" >}}
[CSR_MEM_TEST_SUITE_PASSING]:         {{<relref "/doc/rm/checklist.md#csr-mem-test-suite-passing" >}}
[ALT_TOOL_SETUP]:                     {{<relref "/doc/rm/checklist.md#alt-tool-setup" >}}
[SANITY_REGRESSION_SETUP]:            {{<relref "/doc/rm/checklist.md#sanity-regression-setup" >}}
[NIGHTLY_REGRESSION_SETUP]:           {{<relref "/doc/rm/checklist.md#nightly-regression-setup" >}}
[COVERAGE_MODEL_ADDED]:               {{<relref "/doc/rm/checklist.md#coverage-model-added" >}}
[PRE_VERIFIED_SUB_MODULES_V1]:        {{<relref "/doc/rm/checklist.md#pre-verified-sub-modules-v1" >}}
[DESIGN_SPEC_REVIEWED]:               {{<relref "/doc/rm/checklist.md#design-spec-reviewed" >}}
[DV_PLAN_TESTPLAN_REVIEWED]:          {{<relref "/doc/rm/checklist.md#dv-plan-testplan-reviewed" >}}
[STD_TEST_CATEGORIES_PLANNED]:        {{<relref "/doc/rm/checklist.md#std-test-categories-planned" >}}
[V2_CHECKLIST_SCOPED]:                {{<relref "/doc/rm/checklist.md#v2-checklist-scoped" >}}

### Checklists for milestone V2

 Type         | Item                                    | Resolution  | Note/Collaterals
--------------|-----------------------------------------|-------------|------------------
Documentation | [DESIGN_DELTAS_CAPTURED][]              | Not Started |
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


[DESIGN_DELTAS_CAPTURED]:             {{<relref "/doc/rm/checklist.md#design-deltas-captured" >}}
[DV_PLAN_COMPLETED]:                  {{<relref "/doc/rm/checklist.md#dv-plan-completed"
>}}
[ALL_INTERFACES_EXERCISED]:           {{<relref "/doc/rm/checklist.md#all-interfaces-exercised" >}}
[ALL_ASSERTION_CHECKS_ADDED]:         {{<relref "/doc/rm/checklist.md#all-assertion-checks-added" >}}
[TB_ENV_COMPLETED]:                   {{<relref "/doc/rm/checklist.md#tb-env-completed"
>}}
[ALL_TESTS_PASSING]:                  {{<relref "/doc/rm/checklist.md#all-tests-passing"
>}}
[FW_SIMULATED]:                       {{<relref "/doc/rm/checklist.md#fw-simulated" >}}
[NIGHTLY_REGRESSION_V2]:              {{<relref "/doc/rm/checklist.md#nightly-regression-v2" >}}
[CODE_COVERAGE_V2]:                   {{<relref "/doc/rm/checklist.md#code-coverage-v2"
>}}
[FUNCTIONAL_COVERAGE_V2]:             {{<relref "/doc/rm/checklist.md#functional-coverage-v2" >}}
[NO_HIGH_PRIORITY_ISSUES_PENDING]:    {{<relref "/doc/rm/checklist.md#no-high-priority-issues-pending" >}}
[ALL_LOW_PRIORITY_ISSUES_ROOT_CAUSED]:{{<relref "/doc/rm/checklist.md#all-low-priority-issues-root-caused" >}}
[PRE_VERIFIED_SUB_MODULES_V2]:        {{<relref "/doc/rm/checklist.md#pre-verified-sub-modules-v2" >}}
[V3_CHECKLIST_SCOPED]:                {{<relref "/doc/rm/checklist.md#v3-checklist-scoped" >}}

### Checklists for milestone V3

 Type         | Item                              | Resolution  | Note/Collaterals
--------------|-----------------------------------|-------------|------------------
Documentation | [DESIGN_DELTAS_CAPTURED_IF_ANY][] | Not Started |
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

[DESIGN_DELTAS_CAPTURED_IF_ANY]:{{<relref "/doc/rm/checklist.md#design-deltas-captured-if-any" >}}
[ALL_TODOS_RESOLVED]:           {{<relref "/doc/rm/checklist.md#all-todos-resolved" >}}
[X_PROP_ANALYSIS_COMPLETED]:    {{<relref "/doc/rm/checklist.md#x-prop-analysis-completed" >}}
[NIGHTLY_REGRESSION_AT_100]:    {{<relref "/doc/rm/checklist.md#nightly-regression-at-100" >}}
[CODE_COVERAGE_AT_100]:         {{<relref "/doc/rm/checklist.md#code-coverage-at-100" >}}
[FUNCTIONAL_COVERAGE_AT_100]:   {{<relref "/doc/rm/checklist.md#functional-coverage-at-100" >}}
[NO_ISSUES_PENDING]:            {{<relref "/doc/rm/checklist.md#no-issues-pending" >}}
[NO_TOOL_WARNINGS_THROWN]:      {{<relref "/doc/rm/checklist.md#no-tool-warnings-thrown" >}}
[PRE_VERIFIED_SUB_MODULES_V3]:  {{<relref "/doc/rm/checklist.md#pre-verified-sub-modules-v3" >}}
