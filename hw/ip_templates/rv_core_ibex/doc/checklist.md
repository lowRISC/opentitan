# Ibex Processor Core Checklist

This checklist is for [Hardware Stage][] transitions for the [Ibex Processor Core.](../README.md)
All checklist items refer to the content in the [Checklist.](../../../../doc/project_governance/checklist/README.md)

[Hardware Stage]: ../../../../doc/project_governance/development_stages.md


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


[SPEC_COMPLETE]:              ../../../../doc/project_governance/checklist/README.md#spec_complete
[CSR_DEFINED]:                ../../../../doc/project_governance/checklist/README.md#csr_defined
[CLKRST_CONNECTED]:           ../../../../doc/project_governance/checklist/README.md#clkrst_connected
[IP_TOP]:                     ../../../../doc/project_governance/checklist/README.md#ip_top
[IP_INSTANTIABLE]:            ../../../../doc/project_governance/checklist/README.md#ip_instantiable
[PHYSICAL_MACROS_DEFINED_80]: ../../../../doc/project_governance/checklist/README.md#physical_macros_defined_80
[FUNC_IMPLEMENTED]:           ../../../../doc/project_governance/checklist/README.md#func_implemented
[ASSERT_KNOWN_ADDED]:         ../../../../doc/project_governance/checklist/README.md#assert_known_added
[LINT_SETUP]:                 ../../../../doc/project_governance/checklist/README.md#lint_setup

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

[NEW_FEATURES]:          ../../../../doc/project_governance/checklist/README.md#new_features
[BLOCK_DIAGRAM]:         ../../../../doc/project_governance/checklist/README.md#block_diagram
[DOC_INTERFACE]:         ../../../../doc/project_governance/checklist/README.md#doc_interface
[DOC_INTEGRATION_GUIDE]: ../../../../doc/project_governance/checklist/README.md#doc_integration_guide
[MISSING_FUNC]:          ../../../../doc/project_governance/checklist/README.md#missing_func
[FEATURE_FROZEN]:        ../../../../doc/project_governance/checklist/README.md#feature_frozen
[FEATURE_COMPLETE]:      ../../../../doc/project_governance/checklist/README.md#feature_complete
[PORT_FROZEN]:           ../../../../doc/project_governance/checklist/README.md#port_frozen
[ARCHITECTURE_FROZEN]:   ../../../../doc/project_governance/checklist/README.md#architecture_frozen
[REVIEW_TODO]:           ../../../../doc/project_governance/checklist/README.md#review_todo
[STYLE_X]:               ../../../../doc/project_governance/checklist/README.md#style_x
[CDC_SYNCMACRO]:         ../../../../doc/project_governance/checklist/README.md#cdc_syncmacro
[LINT_PASS]:             ../../../../doc/project_governance/checklist/README.md#lint_pass
[CDC_SETUP]:             ../../../../doc/project_governance/checklist/README.md#cdc_setup
[RDC_SETUP]:             ../../../../doc/project_governance/checklist/README.md#rdc_setup
[AREA_CHECK]:            ../../../../doc/project_governance/checklist/README.md#area_check
[TIMING_CHECK]:          ../../../../doc/project_governance/checklist/README.md#timing_check
[SEC_CM_DOCUMENTED]:     ../../../../doc/project_governance/checklist/README.md#sec_cm_documented

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

[SEC_CM_ASSETS_LISTED]:    ../../../../doc/project_governance/checklist/README.md#sec_cm_assets_listed
[SEC_CM_IMPLEMENTED]:      ../../../../doc/project_governance/checklist/README.md#sec_cm_implemented
[SEC_CM_RND_CNST]:         ../../../../doc/project_governance/checklist/README.md#sec_cm_rnd_cnst
[SEC_CM_NON_RESET_FLOPS]:  ../../../../doc/project_governance/checklist/README.md#sec_cm_non_reset_flops
[SEC_CM_SHADOW_REGS]:      ../../../../doc/project_governance/checklist/README.md#sec_cm_shadow_regs
[SEC_CM_RTL_REVIEWED]:     ../../../../doc/project_governance/checklist/README.md#sec_cm_rtl_reviewed
[SEC_CM_COUNCIL_REVIEWED]: ../../../../doc/project_governance/checklist/README.md#sec_cm_council_reviewed

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

[NEW_FEATURES_D3]:      ../../../../doc/project_governance/checklist/README.md#new_features_d3
[TODO_COMPLETE]:        ../../../../doc/project_governance/checklist/README.md#todo_complete
[LINT_COMPLETE]:        ../../../../doc/project_governance/checklist/README.md#lint_complete
[CDC_COMPLETE]:         ../../../../doc/project_governance/checklist/README.md#cdc_complete
[RDC_COMPLETE]:         ../../../../doc/project_governance/checklist/README.md#rdc_complete
[REVIEW_RTL]:           ../../../../doc/project_governance/checklist/README.md#review_rtl
[REVIEW_DELETED_FF]:    ../../../../doc/project_governance/checklist/README.md#review_deleted_ff
[REVIEW_SW_CHANGE]:     ../../../../doc/project_governance/checklist/README.md#review_sw_change
[REVIEW_SW_ERRATA]:     ../../../../doc/project_governance/checklist/README.md#review_sw_errata

## Verification Checklist

Ibex verification is tracked in the [Ibex documentation](https://ibex-core.readthedocs.io/en/latest/03_reference/verification_stages.html).
Ibex is at **V2S**.

Features specific to rv_core_ibex do not have block-level verification.
Top-level testing suffices for these, see the [rv_core_ibex DV document](../dv/README.md) for more details.

### V1

The V1 checklist may be found in the [Ibex documentation](https://ibex-core.readthedocs.io/en/latest/03_reference/verification_stages.html#v1-checklist).

### V2

The V2 checklist may be found in the [Ibex documentation](https://ibex-core.readthedocs.io/en/latest/03_reference/verification_stages.html#v2-checklist).

### V2S

The V2S checklist may be found in the [Ibex documentation](https://ibex-core.readthedocs.io/en/latest/03_reference/verification_stages.html#v2s-checklist).

### V3

The V3 checklist may be found in the [Ibex documentation](https://ibex-core.readthedocs.io/en/latest/03_reference/verification_stages.html#v3-checklist).
