## DVSim

DVSim is a build and run system written in Python that runs a variety of EDA tool flows.
There are multiple steps involved in running EDA tool flows.
DVSim encapsulates them all to provide a single, standardized command-line interface to launch them.
While DVSim was written to support OpenTitan, it can be used for any ASIC project.

All EDA tool flows on OpenTitan are launched using the DVSim tool.
The following flows are currently supported:

* Simulations
* Coverage Unreachability Analysis (UNR)
* Formal (formal property verification (FPV), and connectivity)
* Lint (semantic and stylistic)
* Synthesis
* CDC
* RDC

# Installation

Clone the OpenTitan repository by following the [Getting Started](https://opentitan.org/guides/getting_started) steps.
The rest of the documentation will assume `$REPO_TOP` as the root of the local OpenTitan repository.
DVSim is located at `$REPO_TOP/util/dvsim/dvsim.py`.

DVSim relies on the following third-party Python libraries:
* **[Hjson](https://hjson.github.io/)**: to parse the Hjson DUT configuration data.
* **[Enlighten](https://python-enlighten.readthedocs.io/en/stable/)**: to track the progress of the EDA tool flows on the console in a readable way.
* **[Mistletoe](https://pypi.org/project/mistletoe)**: to convert Markdown format to HTML, used for testplan descriptions and EDA tool flow reports.
* **[Premailer](https://pypi.org/project/premailer/)**: to inline a block of CSS into the generated HTML report.
* **[Tabulate](https://pypi.org/project/tabulate/)**: to pretty-print tabular data when displaying the report on the console.

These dependencies are already listed in `$REPO_TOP/python_requirements.txt`, which can be installed by running:

```console
python3 -m pip install --user -r $REPO_TOP/python-requirements.txt
```

Note that you may have already done this if you followed the getting started steps.

# Other related documents

* [Testplanner tool](./doc/testplanner.md)
* [Design document](./doc/design_doc.md)
* [Glossary](./doc/glossary.md)

# Bugs

Please see [link](https://github.com/lowRISC/opentitan/issues?q=is%3Aopen+is%3Aissue+label%3ATool%3Advsim) for a list of open bugs and feature requests.
