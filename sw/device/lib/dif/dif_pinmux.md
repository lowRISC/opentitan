---
title: "Pin Multiplexer DIF Checklist"
---

<!--
NOTE: This is a template checklist document that is required to be copied over
to `sw/device/lib/dif/dif_pinmux.md` for a new DIF that transitions
from L0 (Specification) to L1 (Development) stage, and updated as needed.
Once done, please remove this comment before checking it in.
-->
This checklist is for [Development Stage]({{< relref "/doc/project/development_stages.md" >}}) transitions for the [Pin Multiplexer DIF]({{< relref "hw/ip/pinmux/doc" >}}).
All checklist items refer to the content in the [Checklist]({{< relref "/doc/project/checklist.md" >}}).



Type           | Item                 | Resolution  | Note/Collaterals
---------------|----------------------|-------------|------------------
Implementation | [DIF_EXISTS][]       | Done        |
Implementation | [DIF_USED_IN_TREE][] | Not Started |
Tests          | [DIF_TEST_UNIT][]    | Not Started |
Tests          | [DIF_TEST_SMOKE][]   | Not Started |

[DIF_EXISTS]:       {{< relref "/doc/project/checklist.md#dif_exists" >}}
[DIF_USED_IN_TREE]: {{< relref "/doc/project/checklist.md#dif_used_in_tree" >}}
[DIF_TEST_UNIT]:    {{< relref "/doc/project/checklist.md#dif_test_unit" >}}
[DIF_TEST_SMOKE]:   {{< relref "/doc/project/checklist.md#dif_test_smoke" >}}


Type           | Item                        | Resolution  | Note/Collaterals
---------------|-----------------------------|-------------|------------------
Implementation | [DIF_FEATURES][]            | Not Started |
Coordination   | [DIF_HW_USAGE_REVIEWED][]   | Not Started |
Coordination   | [DIF_HW_FEATURE_COMPLETE][] | Not Started | [HW Dashboard]({{< relref "hw" >}})
Implementation | [DIF_HW_PARAMS][]           | Not Started |
Documentation  | [DIF_DOC_HW][]              | Not Started |
Documentation  | [DIF_DOC_API][]             | Not Started |
Code Quality   | [DIF_CODE_STYLE][]          | Not Started |
Coordination   | [DIF_DV_TESTS][]            | Not Started |
Implementation | [DIF_USED_TOCK][]           | Not Started |
Review         | HW IP Usage Reviewer(s)     | Not Started |

[DIF_FEATURES]:            {{< relref "/doc/project/checklist.md#dif_features" >}}
[DIF_HW_USAGE_REVIEWED]:   {{< relref "/doc/project/checklist.md#dif_hw_usage_reviewed" >}}
[DIF_HW_FEATURE_COMPLETE]: {{< relref "/doc/project/checklist.md#dif_hw_feature_complete" >}}
[DIF_HW_PARAMS]:           {{< relref "/doc/project/checklist.md#dif_hw_params" >}}
[DIF_DOC_HW]:              {{< relref "/doc/project/checklist.md#dif_doc_hw" >}}
[DIF_DOC_API]:             {{< relref "/doc/project/checklist.md#dif_doc_api" >}}
[DIF_CODE_STYLE]:          {{< relref "/doc/project/checklist.md#dif_code_style" >}}
[DIF_DV_TESTS]:            {{< relref "/doc/project/checklist.md#dif_dv_tests" >}}
[DIF_USED_TOCK]:           {{< relref "/doc/project/checklist.md#dif_used_tock" >}}


Type           | Item                             | Resolution  | Note/Collaterals
---------------|----------------------------------|-------------|------------------
Coordination   | [DIF_HW_DESIGN_COMPLETE][]       | Not Started |
Coordination   | [DIF_HW_VERIFICATION_COMPLETE][] | Not Started |
Review         | [DIF_REVIEW_C_STABLE][]          | Not Started |
Tests          | [DIF_TEST_UNIT_COMPLETE][]       | Not Started |
Review         | [DIF_TODO_COMPLETE][]            | Not Started |
Review         | [DIF_REVIEW_TOCK_STABLE][]       | Not Started |
Review         | Reviewer(s)                      | Not Started |
Review         | Signoff date                     | Not Started |

[DIF_HW_DESIGN_COMPLETE]:       {{< relref "/doc/project/checklist.md#dif_hw_design_complete" >}}
[DIF_HW_VERIFICATION_COMPLETE]: {{< relref "/doc/project/checklist.md#dif_hw_verification_complete" >}}
[DIF_REVIEW_C_STABLE]:          {{< relref "/doc/project/checklist.md#dif_review_c_stable" >}}
[DIF_TEST_UNIT_COMPLETE]:       {{< relref "/doc/project/checklist.md#dif_test_unit_complete" >}}
[DIF_TODO_COMPLETE]:            {{< relref "/doc/project/checklist.md#dif_todo_complete" >}}
[DIF_REVIEW_TOCK_STABLE]:       {{< relref "/doc/project/checklist.md#dif_review_tock_stable" >}}
