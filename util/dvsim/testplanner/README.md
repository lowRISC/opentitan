---
title: "testplanner tool"
---

testplanner is a Python based tool for parsing DV plans written in Hjson
format into a data structure that can be used for:
* Expanding the DV plan inline within the DV document as a table
* Annotating the regression results with DV plan entries for a document driven DV execution

Please see [DV methodology]({{< relref "doc/ug/dv_methodology/index.md#documentation" >}})
for more details on the rationale and motivation for writing and maintaining dv_plans
in a machine-parsable format (`Hjson`).
This document will focus on the anatomy of a Hjson dv_plan, list of features supported
and some of the ways of using the tool.

## Hjson dv_plan

### DV plan entries
Minimally, the following items are sufficient to adequately capture the
intent of a planned test:
* **name: name of the planned test**

    This is a single `lower_snake_case` string that succinctly describes the intended
    feature being tested. As an example, a smoke test which is typically the
    first test written on a brand new testbench would be simply named `smoke`.

* **milestone: verification milestone**

    This is one of {"`V1`", "`V2`" and "`V3`"}. This allows us to concretely indicate
    that all goals for a particular milestone have been achieved and we can
    transition to the next.

* **desc: description of the planned test**

    A multi-line string that briefly describes the intent of the test. It is
    recommended to add a high level goal, stimulus and checking procedure so
    that the reader gets the full picture of what and how the said feature is being
    tested.

    Full [Markdown]({{< relref "doc/rm/markdown_usage_style" >}}) syntax is supported
    when writing the description.

* **tests: list of actual written tests that maps to this planned test**

    DV plan is written in the initial work stage of the verification
    [life-cycle]({{< relref "doc/project/development_stages#hardware-verification-stages" >}}).
    When the DV engineer gets to actually developing the test, it may not map 1:1 to
    the planned test - it may be possible that an already written test that mapped
    to another planned test also satisfies the current one; OR it may also be
    possible that the planned test needs to be split into multiple smaller tests.
    To cater to these needs, we provide the ability to set a list of actual written
    tests that maps to each planned test. This information will then be used to map
    the regression results and annotate them to the DV plan to generate the final
    table. This list does not have to be populated right away. It can be updated
    as and when tests are written.

If need arises, more entries can be added to this list relatively easily.

dv_plan entries are added using the `entries` key, which is a list that looks
like this:
```hjson
  entries: [
    {
      name: feature1
      milestone: V1
      desc: '''**Goal**: High level goal of this test

            **Stimulus**: Describe the stimulus procedure.

            **Check**: Describe the checking procedure.'''
      tests: ["foo_feature1"]
    }
    {
      name: feature2
      milestone: V2
      desc: '''**Goal**: High level goal of this test

            **Stimulus**: Describe the stimulus procedure.

            **Check**: Describe the checking procedure.'''
      tests: ["foo_feature2_test1",
              "foo_feature2_test2",
              "foo_feature2_test3"]
    }
    ...
  ]
```

### Import shared dv_plans
Typically, there are tests that are common to more that one testbench and can be
made a part of a 'shared' DV plan that each DUT DV plan can simply import. An
example of this is running the automated UVM RAL CSR tests, which applies to
almost all DUTs. This can be done using the `import_dv_plans` key:
```hjson
  import_dv_plans: ["util/dvsim/testplanner/examples/common_testplan.hjson",
                     "hw/dv/tools/csr_testplan.hjson"]
```

Note that the paths to common DV plans are relative to `$REPO_TOP`.

For the sake of discussion below, we will refer to the 'main' or DUT dv_plan
as 'DUT' DV plan and the shared DV plans it imports as 'shared' or 'imported'
dv_plans.

The imported DV plans actually present a problem - how can we set
actual written tests that maps to the shared DV plan entry generically
enough that they apply to more than one DUTs? We currently solve this by
providing wildcards, which are single `lower_snake_case` strings within
braces `'{..}'`. A substitution value (or list of values) for the wildcard
string can be optionally provided in the DUT dv_plan.  Here's an example:

```hjson
-------
  // UART dv_plan:
  name: uart

-------
  // Imported dv_plan:
  {
    name: csr
    ...
    tests: ["{name}{intf}_csr_hw_reset"]
  }
```

In the example above, `{name}` and `{intf}` are wildcards used in the
shared DV plan for which substitution values are to be provided in the
DUT dv_plan.  When the tool parses the DUT DV plan along with the
imported dv_plans, it substitutes the wildcards with the substition
values found in the DUT dv_plan.  If substitution is not available, then
the wildcard is replaced with an empty string.  In the example above,
the list of written test resolves to `["uart_csr_hw_reset"]` after
substituting `{name}` with `uart` and `{intf}` with an empty string.
As many wildcards as needed can be added to the tests in the shared
dv_plans to support as wide usecases as possible across different
testbenches. Moreover, the substitution value can be a list of strings,
in which case, the list of written tests will resolve to all values
being substituted. See example below for illustration:

```hjson
-------
  // Chip dv_plan:
  name: chip
  intf: ["", "_jtag"]
  foo: ["x", "y", "z"]

-------
  // Imported dv_plan:
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

The following examples provided within `util/dvsim/testplanner/examples` can be used as
a starting point.
* **`foo_testplan.hjson`**: DUT dv_plan
* **`common_testplan.hjson`**: shared DV plan imported within the DUT dv_plan
* **`foo_dv_doc.md`**: DUT DV plan imported within the DV document doc in Markdown

In addition, see the [UART DV document]({{< relref "hw/ip/uart/doc/dv" >}}) for a
real 'production' example of inline expansion of an imported DV plan as a table
within the DV document.
The [UART dv_plan](https://github.com/lowRISC/opentitan/blob/master/hw/ip/uart/data/uart_testplan.hjson)
imports the shared DV plans located at `hw/dv/tools/dvsim/dv_plans` area.

### Limitations

The following limitations currently hold:
* Only the DUT DV plan can import shared dv_plans; the imported
  DV plans cannot further import more dv_plans
* All planned test names parsed from the DUT DV plan and all of
  its imported tetsplans need to be unique

## Usage examples

### Standalone tool invocations

Generate the DV plan table in HTML to stdout:
```console
$ util/dvsim/testplanner.py testplanner/examples/foo_testplan.hjson
```

Generate the DV plan table in HTML to a file:
```console
$ util/dvsim/testplanner.py testplanner/examples/foo_testplan.hjson -o /tmp/foo_dv_plan_table.html
```

Generate regression results table in HTML to stdout:
```console
$ util/dvsim/testplanner.py testplanner/examples/foo_testplan.hjson -r testplanner/examples/foo_regr_results.hjson
```

Generate regression results table in HTML to a file:
```console
$ util/dvsim/testplanner.py testplanner/examples/foo_testplan.hjson \
    -r testplanner/examples/foo_regr_results.hjson -o /tmp/foo_regr_results.html
```

### APIs for external tools
The `util/build_docs.py` script invokes the testplanner utility functions
directly to parse the Hjson DV plan and insert a HTML table within the DV
plan document. This is done by invoking:

```console
$ ./util/build_docs.py
```
The output for each DV plan will be saved into `build/docs-generated`.
For example the path to the GPIO IP DV plan is `build/docs-generated/hw/ip/gpio/data/gpio_testplan.hjson.dv_plan`.

See following snippet of code for the APIs in use:
```python
from testplanner import class_defs, dv_plan_utils

  # hjson_dv_plan_path: a string pointing to the path to Hjson dv_plan
  # outbuf: file buffer opened for writing
  DV plan = dv_plan_utils.parse_testplan.hjson_dv_plan_path)
  dv_plan_utils.gen_html_dv_plan_table(dv_plan, outbuf)
```

## Future work
* Allow DUT and imported DV plans have the same name for the planned test as
  long as they are in separate files
  * If the same name exists, then append the list of tests together
* Split the regression results table generation into a separate `dashboard_gen`
  script which will also cater to generating results table for `lint` and `fpv`
