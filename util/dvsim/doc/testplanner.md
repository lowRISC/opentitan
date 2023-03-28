# DVSIM Testplanner tool

`testplanner` is a Python based tool for parsing testplans written in Hjson format into a data structure that can be used for:
* Expanding the testplan inline within the DV document as a table;
* Annotating the simulation results with testplan entries for a document driven DV execution;

Please see [DV methodology](../../../doc/contributing/dv/methodology/README.md#documentation) for more details on the rationale and motivation for writing and maintaining testplans in a machine-parseable format (`Hjson`).
This document will focus on the anatomy of an Hjson testplan, the list of features supported and some of the ways of using the tool.

## Hjson testplan

A testplan consists of a list of planned tests (testpoints) and a list of planned functional coverage items (covergroups).

### Testpoints

A testpoint is an entry in the testplan representing a planned test.
Each testpoint maps one-to-one to a unique feature of the design.
Additionally, a testpoint for each of the [key areas of focus](../../../doc/contributing/dv/methodology/README.md#key-test-focus-areas) (whichever ones are applicable) is also captured in the testplan.

The following attributes are used to define each testpoint, at minimum:
* **name: testpoint name**

    This is a single `lower_snake_case` string that succinctly describes the intended feature being tested.
    As an example, a smoke test, which is typically the first test written for a new testbench would simply be called `smoke`.
    A testpoint that focuses on erasing a page within a `flash_ctrl` bank would be called `page_erase`.
    The recommended naming convention to follow is `<main_feature>_<sub_feature>_<sub_sub_feature_or_type>_...`.
    This is no need to suffix (or prefix) the testpoint name with "test".

* **stage: targeted verification stage**

    This is either `V1`, `V2`, `V2S` or `V3`.
    It helps us track whether all of the testing requirements of a verification stage have been achieved.

* **desc: testpoint description**

    A multi-line string that briefly describes the intent of the test.
    It is recommended, but not always necessary to add a high level goal, stimulus, and the checking procedure so that the reader gets a clear idea of what and how the said feature is going to be tested.

    Full [Markdown](../../../doc/contributing/style_guides/markdown_usage_style.md) syntax is supported when writing the description.

* **tests: list of written test(s) for this testpoint**

    The testplan is written in the initial work stage of the verification [life-cycle](../../../doc/project_governance/development_stages.md#hardware-verification-stages-v).
    Later, when the DV engineer writes the tests, they may not map one-to-one to a testpoint - it may be possible that a written test satisfactorily addresses multiple testpoints; OR it may also be possible that a testpoint needs to be split into multiple smaller tests.
    To cater to these needs, we provide the ability to set a list of written tests for each testpoint.
    It is used to not only indicate the current progress so far into each verification stage, but also map the simulation results to the testpoints to generate the final report table.
    This list is initially empty - it is gradually updated as tests are written.
    Setting this list to `["N/A"]` will prevent this testpoint entry from being mapped to the simulation results.
    The testpoint will however, still show up in the generated testplan table.

* **tags: list of tags relevant for this testpoint**

    Tags represent the need to run the same testpoint under specific conditions, in additional platforms or with a specific set of build / runtime options.
    At the moment, tags are not strictly defined - users are free to come up with their own set of tags.
    The following examples of tags illustrate the usage:

```hjson
  // Run this testpoint on verilator and fpga as well.
  tags: ["verilator", "fpga_cw310"]

  // Run this testpoint in gate level and with poweraware.
  tags: ["gls", "pa"]

  // Run this testpoint with ROM (will use test ROM by default).
  tags: ["rom"]

  // Run this testpoint as a post-Si test vector on the tester.
  tags: ["vector"]
```

    The testplan from the documentation point of view, can be filtered by a tag (or a set of tags), so that the generated testplan table only includes (or excludes) those testpoints.

If the need arises, more attributes may be added relatively easily.

Testpoints are added to the testplan using the `testpoints` key.
Here's an example:
```hjson
  testpoints: [
    {
      name: feature1
      stage: V1
      desc: '''**Goal**: High level goal of this test.

            **Stimulus**: Describe the stimulus procedure.

            **Check**: Describe the checking procedure.'''
      tests: ["foo_feature1"]
    }
    {
      name: feature2
      stage: V2
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
      tags: ["gls"]
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

In addition, see the [UART DV document](../../../hw/ip/uart/dv/README.md) for a 'production' example of inline expansion of an imported testplan as a table within the DV document.
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

Filter the testplan by tags "foo" and "bar":
```console
$ ./util/dvsim/testplanner.py \
    util/dvsim/examples/testplanner/foo_testplan.hjson:foo:bar \
    -s util/dvsim/examples/testplanner/foo_sim_results.hjson

Filter the testplan by excluding the testspoints tagged "foo":
```console
$ ./util/dvsim/testplanner.py \
    util/dvsim/examples/testplanner/foo_testplan.hjson:-foo \
    -s util/dvsim/examples/testplanner/foo_sim_results.hjson
```

To filter by tags, simply append the testplan path with the requested tags with ":" delimiter as shown in the example above.
Prefixing the tag with minus sign ('-') will exclude the testpoints that contain that tag.

Note that the simulations results Hjson file used for mapping the results to the testplan in the examples above (`foo_sim_results.hjson`) is for illustration.
`dvsim` does not generate such a file - it invokes the `Testplan` class APIs directly to map the simulation results.

Generate simulation result tables in HTML to a file:
```console
$ ./util/dvsim/testplanner.py \
    util/dvsim/examples/testplanner/foo_testplan.hjson \
    -s util/dvsim/examples/testplanner/foo_sim_results.hjson \
    -o /tmp/foo_sim_results.html
```

### APIs for external tools
The `util/site/build-docs.sh` script invokes the testplanner utility functions directly to parse the Hjson testplan and insert an HTML table within the DV document.
This is done by invoking:

```sh
./util/site/build-docs.sh serve
```

The `util/mdbook_testplan.py` preprocessor renders any testplan present the `SUMMARY.md` into the documenation.
The complete OpenTitan documentation is rendered locally at `https://0.0.0.0:9000`.

## Future work
* Allow DUT and its imported testplans to have the same testpoint name as long as they are in separate files.
  * The list of written tests are appended from both files.
  * The descriptions are merged - its upto the user to ensure that it is still meaningful after the merge.
  * Conflicting verification stages are flagged as an error.
