---
title: "DVSim"
---

DVSim is a build and run system written in Python that runs a variety of EDA tool flows.
There are multiple steps involved in running EDA tool flows.
DVSim encapsulates them all to provide a single, standardized command-line interface to launch them.
While DVSim was written to support OpenTitan, it can be used for any ASIC project.

All EDA tool flows on OpenTitan are launched using the DVSim tool.
The following flows are currently supported:
- Simulations
- Coverage Unreachability Analysis (UNR)
- Formal (formal property verification (FPV), and connectivity)
- Lint (semantic and stylistic)
- Synthesis
- CDC
- RDC

# Installation

Clone the OpenTitan repository by following the [getting started]({{< relref "doc/getting_started" >}}) steps.
The rest of the documentation will assume `$REPO_TOP` as the root of the local OpenTitan repository.
DVSim is located at `$REPO_TOP/util/dvsim/dvsim.py`.

DVSim relies on the following third-party Python libraries:
- **[Hjson](https://hjson.github.io/)**:
  to parse the Hjson DUT configuration data.

- **[Enlighten](https://python-enlighten.readthedocs.io/en/stable/)**:
  to track the progress of the EDA tool flows on the console in a readable way.

- **[Mistletoe](https://pypi.org/project/mistletoe/0.-1/)**:
  to convert Markdown format to HTML, used for testplan descriptions and EDA tool flow reports.

- **[Premailer](https://pypi.org/project/premailer/)**:
  to inline a block of CSS into the generated HTML report.

- **[Tabulate](https://pypi.org/project/tabulate/)**:
  to pretty-print tabular data when displaying the report on the console.

These dependencies are already listed in `$REPO_TOP/python_requirements.txt`, which can be installed by running:

```console
pip3 install --user -r $REPO_TOP/python-requirements.txt
```

Note that you may have already done this if you followed the getting started steps.

# DVSim design doc

The [design doc]({{< relref "util/dvsim/doc/design_doc.md" >}}) illustrates some of the requirements and motivations that drove the developement of this tool.

# Reference manual

The [reference manual]({{< relref "reference_manual" >}}) provides a detailed technical information about DVSim's internals.
It is suitable for contributors who wish to understand, maintain, and make enhancements to the DVSim codebase.

# User guide

The [user guide]({{< relref "util/dvsim/doc/user_guide.md" >}}) helps new and existing contributors use DVSim effectively.

# Codelabs

The [codelabs]({{< relref "util/dvsim/doc/codelabs.md" >}}) provides exercises to create a new setup from scratch.

# Other related documents

- [Glossary of Terms]({{< relref "glossary" >}})
- [Testplanner tool]({{< relref "testplanner" >}})
- [DVSim Hjson Language User Guide]({{< relref "hjson_guide" >}})

# Bugs

Please see [link](https://github.com/lowRISC/opentitan/issues?q=is%3Aopen+is%3Aissue+label%3ATool%3Advsim) for a list of open bugs and feature requests.
