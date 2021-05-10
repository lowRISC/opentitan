---
title: "Testplanner tool"
---

`testplanner` is a Python based tool for parsing testplans written in Hjson format into a data structure that can be used for:
* Expanding the testplan inline within the DV document as a table;
* Annotating the simulation results with testplan entries for a document driven DV execution;

Please see [DV methodology]({{< relref "doc/ug/dv_methodology/index.md#documentation" >}}) for more details on the rationale and motivation for writing and maintaining testplans in a machine-parsable format (`Hjson`).
This document will focus on the anatomy of an Hjson testplan, the list of features supported and some of the ways of using the tool.

## Hjson testplan

A testplan consists of a list of planned tests (testpoints) and a list of planned functional coverage items (covergroups).

### Testpoints

A testpoint is an entry in the testplan representing a planned test.
Each testpoint maps one-to-one to a unique feature of the design.
Additionally, a testpoint for each of the [key areas of focus]({{< relref "doc/ug/dv_methodology/index.md#key-test-focus-areas" >}}) (whichever ones are applicable) is also captured in the testplan.

The following attributes are used to define each testpoint, at minimum:
* **name: testpoint name**

    This is a single `lower_snake_case` string that succinctly describes the intended feature being tested.
    As an example, a smoke test, which is typically the first test written for a new testbench would simply be called `smoke`.
    A testpoint that focuses on erasing a page within a `flash_ctrl` bank would be called `page_erase`.
    The recommended naming convention to follow is `<main_feature>_<sub_feature>_<sub_sub_feature_or_type>_...`.
    This is no need to suffix (or prefix) the testpoint name with "test".

* **milestone: targeted verification milestone**

    This is either `V1`, `V2` or `V3`.
    It helps us track whether all of the testing requirements of a milestone have been achieved.

* **desc: testpoint description**

    A multi-line string that briefly describes the intent of the test.
    It is recommended, but not always necessary to add a high level goal, stimulus, and the checking procedure so that the reader gets a clear idea of what and how the said feature is going to be tested.

    Full [Markdown]({{< relref "doc/rm/markdown_usage_style" >}}) syntax is supported when writing the description.

* **tests: list of written test(s) for a testpoint**

    The testplan is written in the initial work stage of the verification [life-cycle]({{< relref "doc/project/development_stages#hardware-verification-stages" >}}).
    Later, when the DV engineer writes the tests, they may not map one-to-one to a testpoint - it may be possible that a written test satisfactorilly addresses multiple testpoints; OR it may also be possible that a testpoint needs to be split into multiple smaller tests.
    To cater to these needs, we provide the ability to set a list of written tests for each testpoint.
    It is used to not only indicate the current progress so far into each milestone, but also map the simulation results to the testpoints to generate the final report table.
    This list is initially empty - it is gradually updated as tests are written.

If the need arises, more attributes may be added relatively easily.

Testpoints are added to the testplan using the `testpoints` key.
Here's an example:
```hjson
  testpoints: [
    {
      name: feature1
      milestone: V1
      desc: '''**Goal**: High level goal of this test.

            **Stimulus**: Describe the stimulus procedure.

            **Check**: Describe the checking procedure.'''
      tests: ["foo_feature1"]
    }
    {
      name: feature2
      milestone: V2
      desc: '''**Goal**: High level goal of this test.

            **Stimulus**: Describe the stimulus procedure.

            **Check**: Describe the checking procedure.'''

      // Below is the list of written (runnable) tests that maps to `feature2`.
      // To satisfactorilly test `feature2`, three tests are written. There
      // could be various reasons to split the written test, the most common
      // being unacceptably long runtime.
      tests: ["foo_feature2_test1",
              "foo_feature2_test2",
              "foo_feature2_test3"]
    }
    ...
  ]
```

### Covergroups

A list of covergroups documented in the testplan represents the functional coverage plan for the design.

The following attributes are used to define each covergroup:
* **name: name of the covergroup**

    This is a single `lower_snake_case` string that succinctly describes the covergroup.
    It needs to map to the actual written covergroup, so that it can be audited from the simulation results for tracking.
    As indicated in our DV style guide, the covergroup name is suffixed with `_cg`.

* **desc: description of the covergroup**

    A multi-line string that briefly describes what functionality is captured by the covergroup.
    It is recommended, but not necessary to list the individual coverpoints and crosses to ease the review.

Covergroups are added to the testplan using the `covergroups` key.
Here's an example:
```hjson
  covergroups: [
    {
      name: timer_cg
      desc: '''Cover various combinations of rv_timer inputs when generating a
            timeout. Cover appropriate ranges of values of step and prescaler
            as coverpoint buckets and cross them with each other.
            '''
    }
    ...
  ]
```
### Import shared testplans

Typically, there are tests that are common to more than one testbench and can be made a part of a 'shared' testplan that each DUT testplan can simply import.
An example of this is running the automated UVM RAL CSR tests, which applies to almost all DUTs.
This is achieved using the `import_testplans` key:
```hjson
  import_testplans: ["util/dvsim/examples/testplanner/common_testplan.hjson",
                     "hw/dv/tools/csr_testplan.hjson"]
```

Note that the paths to common testplans are relative to `$REPO_TOP`.

For the sake of discussion below, we will refer to the 'main' or DUT testplan as the 'DUT' testplan and the shared testplans it imports as 'shared' or 'imported' testplans.

The imported testplans actually present a problem: how can the written tests that map to the shared testpoint be generic enough that they apply to multiple DUTs?
We currently solve this by providing substitution wildcards.
These are single `lower_snake_case` strings indicated within braces `'{..}'`.
A substitution value (or list of values) for the wildcard string is optionally provided in the DUT testplan.

Here's an example:
```hjson
-------
  // UART testplan:
  name: uart

-------
  // Imported testplan:
  {
    name: csr
    ...
    tests: ["{name}{intf}_csr_hw_reset"]
  }
```

In the example above, `{name}` and `{intf}` are wildcards used in the shared testplan for which substitution values are to be provided in the DUT testplan.
When the tool parses the DUT testplan along with its imported testplans, it replaces the wildcards with its substitution values found in the DUT testplan.
If a substitution is not available, the wildcard is replaced with an empty string.
In the example above, the list of written tests resolves to `["uart_csr_hw_reset"]` after substituting `{name}` with `uart` and `{intf}` with an empty string.
As many wildcards as needed can be added to tests in the shared testplans to support the various usecases across different testbenches.
Also, the substitution value can be a list of strings, in which case, the list of written tests expands to all possible combinations of values.

Here's an example:
```hjson
-------
  // Chip testplan:
  name: chip
  intf: ["", "_jtag"]
  foo: ["x", "y", "z"]

-------
  // Imported testplan:
  {
    name: csr
    ...
    tests: ["{name}{intf}_csr_hw_reset_{foo}"]
  }
```

This will resolve to the following 6 tests:

```
["chip_csr_hw_reset_x", "chip_csr_hw_reset_y", "chip_csr_hw_reset_z",
 "chip_jtag_csr_hw_reset_x", "chip_jtag_csr_hw_reset_y", "chip_jtag_csr_hw_reset_z"]
```

### Example sources

The following examples provided within `util/dvsim/examples/testplanner` can be used as a starting point.
* **`foo_testplan.hjson`**: DUT testplan
* **`common_testplan.hjson`**: shared testplan imported within the DUT testplan
* **`foo_dv_doc.md`**: DUT testplan imported within the DV document doc in Markdown

In addition, see the [UART DV document]({{< relref "hw/ip/uart/doc/dv" >}}) for a 'production' example of inline expansion of an imported testplan as a table within the DV document.
The [UART testplan](https://github.com/lowRISC/opentitan/blob/master/hw/ip/uart/data/uart_testplan.hjson) imports some of the shared testplans located at `hw/dv/tools/dvsim/testplans` area.

### Limitations

The following limitations currently hold:
* Only the DUT testplan can import shared testplans; the imported testplans cannot further import more testplans.
* All planned test names parsed from the DUT testplan and all of its imported testplans need to be unique.

## Usage examples

### Standalone tool invocations

Generate the testplan table in HTML to stdout:
```console
$ cd $REPO_TOP
$ ./util/dvsim/testplanner.py \
    util/dvsim/examples/testplanner/foo_testplan.hjson
```

Generate the testplan table in HTML to a file:
```console
$ ./util/dvsim/testplanner.py \
    util/dvsim/examples/testplanner/foo_testplan.hjson \
    -o /tmp/foo_testplan_table.html
```

Generate simulation result tables in HTML to stdout:
```console
$ ./util/dvsim/testplanner.py \
    util/dvsim/examples/testplanner/foo_testplan.hjson \
    -s util/dvsim/examples/testplanner/foo_sim_results.hjson
```

Note that the simulations results HJson file used for mapping the results to the testplan is for illustration.
`dvsim` does not generate such a file - it invokes the `Testplan` class APIs directly to map the simulation results.

Generate simulation result tables in HTML to a file:
```console
$ ./util/dvsim/testplanner.py \
    util/dvsim/examples/testplanner/foo_testplan.hjson \
    -s util/dvsim/examples/testplanner/foo_sim_results.hjson \
    -o /tmp/foo_sim_results.html
```

### APIs for external tools
The `util/build_docs.py` script invokes the testplanner utility functions directly to parse the Hjson testplan and insert an HTML table within the DV document.
This is done by invoking:
```console
$ ./util/build_docs.py --preview
```
The output for each testplan will be saved into `build/docs-generated`.
For example the GPIO IP testplan is rendered into a table at `build/docs-generated/hw/ip/gpio/data/gpio_testplan.hjson.testplan`.
The complete OpenTitan documentation is rendered locally at `https://localhost:1313`.

The following snippet of code can be found in `util/build_docs.py`:
```python
from dvsim.Testplan import Testplan

  # hjson_testplan_path: a string pointing to the path to Hjson testplan
  testplan = Testplan(hjson_testplan_path)
  text = testplan.get_testplan_table("html")
```

## Future work
* Allow DUT and its imported testplans to have the same testpoint name as long as they are in separate files.
  * The list of written tests are appended from both files.
  * The descriptions are merged - its upto the user to ensure that it is still meaningful after the merge.
  * Conflicting milestones are flagged as an error.
