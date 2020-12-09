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
Review        | Reviewer(s)                    | Done        | @weicaiyang @aytong @martin-lueker
Review        | Signoff date                   | Done        | 2019-11-04

[TL-UL Spec]:         {{<relref "/hw/ip/tlul/doc">}}
[crossbar_tool]:      {{<relref "/doc/rm/crossbar_tool">}}

[SPEC_COMPLETE]:              {{<relref "/doc/project/checklist.md#spec-complete" >}}
[CSR_DEFINED]:                {{<relref "/doc/project/checklist.md#csr-defined" >}}
[CLKRST_CONNECTED]:           {{<relref "/doc/project/checklist.md#clkrst-connected" >}}
[IP_TOP]:                     {{<relref "/doc/project/checklist.md#ip-top" >}}
[IP_INSTANTIABLE]:            {{<relref "/doc/project/checklist.md#ip-instantiable" >}}
[PHYSICAL_MACROS_DEFINED_80]: {{<relref "/doc/project/checklist.md#physical_macros_defined-80" >}}
[FUNC_IMPLEMENTED]:           {{<relref "/doc/project/checklist.md#func-implemented" >}}
[ASSERT_KNOWN_ADDED]:         {{<relref "/doc/project/checklist.md#assert-known-added" >}}
[LINT_SETUP]:                 {{<relref "/doc/project/checklist.md#lint-setup" >}}

### D2

Type          | Item                    | Resolution  | Note/Collaterals
--------------|-------------------------|-------------|------------------
Documentation | [NEW_FEATURES][]        | N/A         |
Documentation | [BLOCK_DIAGRAM][]       | Done        |
Documentation | [DOC_INTERFACE][]       | N/A         |
Documentation | [MISSING_FUNC][]        | N/A         |
Documentation | [FEATURE_FROZEN][]      | Done        |
RTL           | [FEATURE_COMPLETE][]    | Done        |
RTL           | [AREA_CHECK][]          | Done        |
RTL           | [PORT_FROZEN][]         | Done        | Targetting for current top_earlgrey( Port can be changed later based on top_earlgrey config)
RTL           | [ARCHITECTURE_FROZEN][] | Done        |
RTL           | [REVIEW_TODO][]         | Done        | PR [#837][] is pending
RTL           | [STYLE_X][]             | Done        |
Code Quality  | [LINT_PASS][]           | Done        |
Code Quality  | [CDC_SETUP][]           | N/A         | top_earlgrey uses single clock at this moment. (new PR by Tim is pending )
Code Quality  | [FPGA_TIMING][]         | Done        | Pipeline inserted in front of Core IBEX. meet timing @ 50MHz on NexysVideo
Code Quality  | [CDC_SYNCMACRO][]       | N/A         |
Security      | [SEC_CM_IMPLEMENTED][]  | N/A         |
Security      | [SEC_NON_RESET_FLOPS][] | N/A         |
Security      | [SEC_SHADOW_REGS][]     | N/A         |
Review        | Reviewer(s)             | Done        | @sjgitty @weicaiyang
Review        | Signoff date            | Done        | 2019-11-04

[#837]: https://github.com/lowRISC/opentitan/pull/837

[NEW_FEATURES]:        {{<relref "/doc/project/checklist.md#new-features" >}}
[BLOCK_DIAGRAM]:       {{<relref "/doc/project/checklist.md#block-diagram" >}}
[DOC_INTERFACE]:       {{<relref "/doc/project/checklist.md#doc-interface" >}}
[MISSING_FUNC]:        {{<relref "/doc/project/checklist.md#missing-func" >}}
[FEATURE_FROZEN]:      {{<relref "/doc/project/checklist.md#feature-frozen" >}}
[FEATURE_COMPLETE]:    {{<relref "/doc/project/checklist.md#feature-complete" >}}
[AREA_CHECK]:          {{<relref "/doc/project/checklist.md#area-check" >}}
[PORT_FROZEN]:         {{<relref "/doc/project/checklist.md#port-frozen" >}}
[ARCHITECTURE_FROZEN]: {{<relref "/doc/project/checklist.md#architecture-frozen" >}}
[REVIEW_TODO]:         {{<relref "/doc/project/checklist.md#review-todo" >}}
[STYLE_X]:             {{<relref "/doc/project/checklist.md#style-x" >}}
[LINT_PASS]:           {{<relref "/doc/project/checklist.md#lint-pass" >}}
[CDC_SETUP]:           {{<relref "/doc/project/checklist.md#cdc-setup" >}}
[CDC_SYNCMACRO]:       {{<relref "/doc/project/checklist.md#cdc-syncmacro" >}}
[FPGA_TIMING]:         {{<relref "/doc/project/checklist.md#fpga-timing" >}}
[SEC_CM_IMPLEMENTED]:  {{<relref "/doc/project/checklist.md#sec-cm-implemented" >}}
[SEC_NON_RESET_FLOPS]: {{<relref "/doc/project/checklist.md#sec-non-reset-flops" >}}
[SEC_SHADOW_REGS]:     {{<relref "/doc/project/checklist.md#sec-shadow-regs" >}}

### D3

 Type         | Item                    | Resolution  | Note/Collaterals
--------------|-------------------------|-------------|------------------
Documentation | [NEW_FEATURES_D3][]     | N/A         |
RTL           | [TODO_COMPLETE][]       | Done        | Resolved: [#837][]
Code Quality  | [LINT_COMPLETE][]       | Done        |
Code Quality  | [CDC_COMPLETE][]        | N/A         |
Review        | [REVIEW_RTL][]          | Done        | 1st @tjaychen / 2nd @martin-lueker
Review        | [REVIEW_DELETED_FF][]   | N/A         |
Review        | [REVIEW_SW_CSR][]       | N/A         |
Review        | [REVIEW_SW_FATAL_ERR][] | Done        |
Review        | [REVIEW_SW_CHANGE][]    | N/A         |
Review        | [REVIEW_SW_ERRATA][]    | Done        |
Review        | Reviewer(s)             | Done        | @weicaiyang @tjaychen
Review        | Signoff date            | Done        | 2019-11-07

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
Documentation | [DV_DOC_DRAFT_COMPLETED][]            | Done        | [DV_PLAN][]
Documentation | [DV_PLAN_COMPLETED][]                 | Done        |
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
Review        | [DV_PLAN_REVIEWED][]                  | Done        |
Review        | [STD_TEST_CATEGORIES_PLANNED][]       | Done        | Exception (Security, Power, Debug, Performance)
Review        | [V2_CHECKLIST_SCOPED][]               | Done        |
Review        | Reviewer(s)                           | Done        | @eunchan @sjgitty @sriyerg
Review        | Signoff date                          | Done        | 2019-11-04


[DV_PLAN]:                            {{<relref "/hw/ip/tlul/doc/dv">}}

[DV_DOC_DRAFT_COMPLETED]:             {{<relref "/doc/project/checklist.md#dv-plan-draft-completed" >}}
[DV_PLAN_COMPLETED]:                  {{<relref "/doc/project/checklist.md#dv_plan-completed" >}}
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
[TB_LINT_setup]:                      {{<relref "/doc/project/checklist.md#tb_lint_setup" >}}
[PRE_VERIFIED_SUB_MODULES_V1]:        {{<relref "/doc/project/checklist.md#pre-verified-sub-modules-v1" >}}
[DESIGN_SPEC_REVIEWED]:               {{<relref "/doc/project/checklist.md#design-spec-reviewed" >}}
[DV_PLAN_REVIEWED]:                   {{<relref "/doc/project/checklist.md#dv-plan-dv_plan-reviewed" >}}
[STD_TEST_CATEGORIES_PLANNED]:        {{<relref "/doc/project/checklist.md#std-test-categories-planned" >}}
[V2_CHECKLIST_SCOPED]:                {{<relref "/doc/project/checklist.md#v2-checklist-scoped" >}}

### V2

 Type         | Item                                    | Resolution  | Note/Collaterals
--------------|-----------------------------------------|-------------|------------------
Documentation | [DESIGN_DELTAS_CAPTURED_V2][]           | N/A         |
Documentation | [DV_PLAN_COMPLETED][]                   | Done        |
Testbench     | [ALL_INTERFACES_EXERCISED][]            | Done        |
Testbench     | [ALL_ASSERTION_CHECKS_ADDED][]          | Done        |
Testbench     | [TB_ENV_COMPLETED][]                    | Done        |
Tests         | [ALL_TESTS_PASSING][]                   | Done        |
Tests         | [FW_SIMULATED][]                        | N/A         |
Regression    | [NIGHTLY_REGRESSION_V2][]               | Done        |
Coverage      | [CODE_COVERAGE_V2][]                    | Done        |
Coverage      | [FUNCTIONAL_COVERAGE_V2][]              | Done        |
Code Quality  | [TB_LINT_PASS][]                        | Done        |
Issues        | [NO_HIGH_PRIORITY_ISSUES_PENDING][]     | Done        |
Issues        | [ALL_LOW_PRIORITY_ISSUES_ROOT_CAUSED][] | Done        |
Integration   | [PRE_VERIFIED_SUB_MODULES_V2][]         | Waived      | prim_arbiter to be verified later
Review        | [V3_CHECKLIST_SCOPED][]                 | Done        |
Review        | Reviewer(s)                             | Done        | @eunchan @sjgitty @sriyerg
Review        | Signoff date                            | Done        | 2019-11-04


[DESIGN_DELTAS_CAPTURED_V2]:          {{<relref "/doc/project/checklist.md#design-deltas-captured-v2" >}}
[DV_PLAN_COMPLETED]:                  {{<relref "/doc/project/checklist.md#dv-plan-completed" >}}
[ALL_INTERFACES_EXERCISED]:           {{<relref "/doc/project/checklist.md#all-interfaces-exercised" >}}
[ALL_ASSERTION_CHECKS_ADDED]:         {{<relref "/doc/project/checklist.md#all-assertion-checks-added" >}}
[TB_ENV_COMPLETED]:                   {{<relref "/doc/project/checklist.md#tb-env-completed" >}}
[ALL_TESTS_PASSING]:                  {{<relref "/doc/project/checklist.md#all-tests-passing" >}}
[FW_SIMULATED]:                       {{<relref "/doc/project/checklist.md#fw-simulated" >}}
[NIGHTLY_REGRESSION_V2]:              {{<relref "/doc/project/checklist.md#nightly-regression-v2" >}}
[CODE_COVERAGE_V2]:                   {{<relref "/doc/project/checklist.md#code-coverage-v2" >}}
[FUNCTIONAL_COVERAGE_V2]:             {{<relref "/doc/project/checklist.md#functional-coverage-v2" >}}
[TB_LINT_PASS]:                       {{<relref "/doc/project/checklist.md#tb_lint_pass" >}}
[NO_HIGH_PRIORITY_ISSUES_PENDING]:    {{<relref "/doc/project/checklist.md#no-high-priority-issues-pending" >}}
[ALL_LOW_PRIORITY_ISSUES_ROOT_CAUSED]:{{<relref "/doc/project/checklist.md#all-low-priority-issues-root-caused" >}}
[PRE_VERIFIED_SUB_MODULES_V2]:        {{<relref "/doc/project/checklist.md#pre-verified-sub-modules-v2" >}}
[V3_CHECKLIST_SCOPED]:                {{<relref "/doc/project/checklist.md#v3-checklist-scoped" >}}

### V3

 Type         | Item                              | Resolution  | Note/Collaterals
--------------|-----------------------------------|-------------|------------------
Documentation | [DESIGN_DELTAS_CAPTURED_V3][]     | N/A         |
Testbench     | [ALL_TODOS_RESOLVED][]            | Done        |
Tests         | [X_PROP_ANALYSIS_COMPLETED][]     | Waived      | tool setup in progress
Regression    | [NIGHTLY_REGRESSION_AT_100][]     | Done        |
Coverage      | [CODE_COVERAGE_AT_100][]          | Done        | [xbar_cov_excl.el][]
Coverage      | [FUNCTIONAL_COVERAGE_AT_100][]    | Done        |
Issues        | [NO_ISSUES_PENDING][]             | Done        |
Code Quality  | [NO_TOOL_WARNINGS_THROWN][]       | Done        | Waived warning due to using 'force' to connect the signal
Code Quality  | [TB_LINT_COMPLETE][]              | Not Started |
Integration   | [PRE_VERIFIED_SUB_MODULES_V3][]   | Waived      | prim_arbiter to be verified later
Review        | Reviewer(s)                       | Done        | @eunchan @sriyerg
Review        | Signoff date                      | Done        | 2019-11-07

[DESIGN_DELTAS_CAPTURED_V3]:    {{<relref "/doc/project/checklist.md#design-deltas-captured-v3" >}}
[ALL_TODOS_RESOLVED]:           {{<relref "/doc/project/checklist.md#all-todos-resolved" >}}
[X_PROP_ANALYSIS_COMPLETED]:    {{<relref "/doc/project/checklist.md#x-prop-analysis-completed" >}}
[NIGHTLY_REGRESSION_AT_100]:    {{<relref "/doc/project/checklist.md#nightly-regression-at-100" >}}
[CODE_COVERAGE_AT_100]:         {{<relref "/doc/project/checklist.md#code-coverage-at-100" >}}
[FUNCTIONAL_COVERAGE_AT_100]:   {{<relref "/doc/project/checklist.md#functional-coverage-at-100" >}}
[NO_ISSUES_PENDING]:            {{<relref "/doc/project/checklist.md#no-issues-pending" >}}
[NO_TOOL_WARNINGS_THROWN]:      {{<relref "/doc/project/checklist.md#no-tool-warnings-thrown" >}}
[TB_LINT_COMPLETE]:             {{<relref "/doc/project/checklist.md#tb_lint_complete" >}}
[PRE_VERIFIED_SUB_MODULES_V3]:  {{<relref "/doc/project/checklist.md#pre-verified-sub-modules-v3" >}}
[xbar_cov_excl.el]: https://github.com/weicaiyang/opentitan/blob/6cd55ad23aac96374bfa0bec315b904c6ffbdb8f/hw/ip/tlul/dv/cov/xbar_cov_excl.el
