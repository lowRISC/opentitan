---
title: "Ibex Processor Core Checklist"
---

This checklist is for [Hardware Stage][] transitions for the [Ibex Processor Core.](../)
All checklist items refer to the content in the [Checklist.]({{<relref "/doc/project/checklist.md">}})

[Hardware Stage]: {{<relref "/doc/project/development_stages.md" >}}


## Design Checklist

### D1

Type          | Item                           | Resolution  | Note/Collaterals
--------------|--------------------------------|-------------|------------------
Documentation | [SPEC_COMPLETE][]              | Done        |
Documentation | [CSR_DEFINED][]                | Done        | lowRISC/ibex#307
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

[PHYSICAL_MACROS_DEFINED_80][] is waived as Ibex doesn't have memories inside.

### D2

Type          | Item                      | Resolution  | Note/Collaterals
--------------|---------------------------|-------------|------------------
Documentation | [NEW_FEATURES][]          | N/A         |
Documentation | [BLOCK_DIAGRAM][]         | Done        |
Documentation | [DOC_INTERFACE][]         | Done        |
Documentation | [DOC_INTEGRATION_GUIDE][] | Waived      | This checklist item has been added retrospectively.
Documentation | [MISSING_FUNC][]          | N/A         |
Documentation | [FEATURE_FROZEN][]        | Done        |
RTL           | [FEATURE_COMPLETE][]      | Done        |
RTL           | [PORT_FROZEN][]           | Done        |
RTL           | [ARCHITECTURE_FROZEN][]   | Done        |
RTL           | [REVIEW_TODO][]           | Done        | Minor TODOs remain, waived
RTL           | [STYLE_X][]               | Done        | will be reworked (#366)
RTL           | [CDC_SYNCMACRO][]         | Done        |
Code Quality  | [LINT_PASS][]             | Done        | Lint waivers created, not finalized
Code Quality  | [CDC_SETUP][]             | Waived      | No block-level flow available - waived to top-level signoff.
Code Quality  | [RDC_SETUP][]             | Waived      | No block-level flow available - waived to top-level signoff.
Code Quality  | [AREA_CHECK][]            | Done        | Area smoke check done (on FPGA)
Code Quality  | [TIMING_CHECK][]          | Done        | FPGA timing acceptable
Security      | [SEC_CM_DOCUMENTED][]     | Done        |

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
Security      | [SEC_CM_ASSETS_LISTED][]     | Done        |
Security      | [SEC_CM_IMPLEMENTED][]       | Done        |
Security      | [SEC_CM_RND_CNST][]          | Done        |
Security      | [SEC_CM_NON_RESET_FLOPS][]   | Done        |
Security      | [SEC_CM_SHADOW_REGS][]       | Done        |
Security      | [SEC_CM_RTL_REVIEWED][]      | Done        |
Security      | [SEC_CM_COUNCIL_REVIEWED][]  | Done        |

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
Documentation | [NEW_FEATURES_D3][]     | Not Started |
RTL           | [TODO_COMPLETE][]       | Not Started |
Code Quality  | [LINT_COMPLETE][]       | Not Started |
Code Quality  | [CDC_COMPLETE][]        | Not Started |
Code Quality  | [RDC_COMPLETE][]        | Not Started |
Review        | [REVIEW_RTL][]          | Not Started |
Review        | [REVIEW_DELETED_FF][]   | Not Started |
Review        | [REVIEW_SW_CHANGE][]    | Not Started |
Review        | [REVIEW_SW_ERRATA][]    | Not Started |

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

Ibex verification is tracked in the [Ibex documentation](https://ibex-core.readthedocs.io/en/latest/03_reference/verification_stages.html).
Ibex is at **V2S**.

Features specific to rv_core_ibex do not have block-level verification.
Top-level testing suffices for these, see the [rv_core_ibex DV document]({{<relref "hw/ip/rv_core_ibex/doc/dv/" >}}) for more details.

### V1

The V1 checklist may be found in the [Ibex documentation](https://ibex-core.readthedocs.io/en/latest/03_reference/verification_stages.html#v1-checklist).

### V2

The V2 checklist may be found in the [Ibex documentation](https://ibex-core.readthedocs.io/en/latest/03_reference/verification_stages.html#v2-checklist).

### V2S

The V2S checklist may be found in the [Ibex documentation](https://ibex-core.readthedocs.io/en/latest/03_reference/verification_stages.html#v2s-checklist).

### V3

The V3 checklist may be found in the [Ibex documentation](https://ibex-core.readthedocs.io/en/latest/03_reference/verification_stages.html#v3-checklist).
