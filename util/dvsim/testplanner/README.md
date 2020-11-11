---
title: "Testplanner tool"
---

Testplanner is a Python based tool for parsing testplans written in Hjson
format into a data structure that can be used for:
* Expanding the testplan inline within the DV plan as a table
* Annotating the regression results with testplan entries for a document driven DV execution

Please see [DV methodology]({{< relref "doc/ug/dv_methodology/index.md#documentation" >}})
for more details on the rationale and motivation for writing and maintaining testplans
in a machine-parsable format (`Hjson`).
This document will focus on the anatomy of a Hjson testplan, list of features supported
and some of the ways of using the tool.

## Hjson Testplan

### Testplan entries
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

    Testplan is written in the initial work stage of the verification
    [life-cycle]({{< relref "doc/project/development_stages#hardware-verification-stages" >}}).
    When the DV engineer gets to actually developing the test, it may not map 1:1 to
    the planned test - it may be possible that an already written test that mapped
    to another planned test also satisfies the current one; OR it may also be
    possible that the planned test needs to be split into multiple smaller tests.
    To cater to these needs, we provide the ability to set a list of actual written
    tests that maps to each planned test. This information will then be used to map
    the regression results and annotate them to the testplan to generate the final
    table. This list does not have to be populated right away. It can be updated
    as and when tests are written.

If need arises, more entries can be added to this list relatively easily.

Testplan entries are added using the `entries` key, which is a list that looks
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

### Import shared testplans
Typically, there are tests that are common to more that one testbench and can be
made a part of a 'shared' testplan that each DUT testplan can simply import. An
example of this is running the automated UVM RAL CSR tests, which applies to
almost all DUTs. This can be done using the `import_testplans` key:
```hjson
  import_testplans: ["util/dvsim/testplanner/examples/common_testplan.hjson",
                     "hw/dv/tools/csr_testplan.hjson"]
```

Note that the paths to common testplans are relative to `$REPO_TOP`.

For the sake of discussion below, we will refer to the 'main' or DUT testplan
as 'DUT' testplan and the shared testplans it imports as 'shared' or 'imported'
testplans.

The imported testplans actually present a problem - how can we set
actual written tests that maps to the shared testplan entry generically
enough that they apply to more than one DUTs? We currently solve this by
providing wildcards, which are single `lower_snake_case` strings within
braces `'{..}'`. A substitution value (or list of values) for the wildcard
string can be optionally provided in the DUT testplan.  Here's an example:

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

In the example above, `{name}` and `{intf}` are wildcards used in the
shared testplan for which substitution values are to be provided in the
DUT testplan.  When the tool parses the DUT testplan along with the
imported testplans, it substitutes the wildcards with the substition
values found in the DUT testplan.  If substitution is not available, then
the wildcard is replaced with an empty string.  In the example above,
the list of written test resolves to `["uart_csr_hw_reset"]` after
substituting `{name}` with `uart` and `{intf}` with an empty string.
As many wildcards as needed can be added to the tests in the shared
testplans to support as wide usecases as possible across different
testbenches. Moreover, the substitution value can be a list of strings,
in which case, the list of written tests will resolve to all values
being substituted. See example below for illustration:

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

The following examples provided within `util/dvsim/testplanner/examples` can be used as
a starting point.
* **`foo_testplan.hjson`**: DUT testplan
* **`common_testplan.hjson`**: shared testplan imported within the DUT testplan
* **`foo_dv_plan.md`**: DUT testplan imported within the DV plan doc in Markdown

In addition, see the [UART DV Plan]({{< relref "hw/ip/uart/doc/dv_plan" >}}) for a
real 'production' example of inline expansion of an imported testplan as a table
within the DV Plan document.
The [UART testplan](https://github.com/lowRISC/opentitan/blob/master/hw/ip/uart/data/uart_testplan.hjson)
imports the shared testplans located at `hw/dv/tools/dvsim/testplans` area.

### Limitations

The following limitations currently hold:
* Only the DUT testplan can import shared testplans; the imported
  testplans cannot further import more testplans
* All planned test names parsed from the DUT testplan and all of
  its imported tetsplans need to be unique

## Usage examples

### Standalone tool invocations

Generate the testplan table in HTML to stdout:
```console
$ util/dvsim/testplanner.py testplanner/examples/foo_testplan.hjson
```

Generate the testplan table in HTML to a file:
```console
$ util/dvsim/testplanner.py testplanner/examples/foo_testplan.hjson -o /tmp/foo_testplan_table.html
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
directly to parse the Hjson testplan and insert a HTML table within the DV
plan document. This is done by invoking:

```console
$ ./util/build_docs.py
```
The output for each testplan will be saved into `build/docs-generated`.
For example the path to the GPIO IP testplan is `build/docs-generated/hw/ip/gpio/data/gpio_testplan.hjson.testplan`.

See following snippet of code for the APIs in use:
```python
from testplanner import class_defs, testplan_utils

  # hjson_testplan_path: a string pointing to the path to Hjson testplan
  # outbuf: file buffer opened for writing
  testplan = testplan_utils.parse_testplan(hjson_testplan_path)
  testplan_utils.gen_html_testplan_table(testplan, outbuf)
```

## Future work
* Allow DUT and imported testplans have the same name for the planned test as
  long as they are in separate files
  * If the same name exists, then append the list of tests together
* Split the regression results table generation into a separate `dashboard_gen`
  script which will also cater to generating results table for `lint` and `fpv`
